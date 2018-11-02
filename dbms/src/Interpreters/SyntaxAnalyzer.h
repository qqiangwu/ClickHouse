#pragma once

#include <Interpreters/AnalyzedJoin.h>

namespace DB
{

struct SyntaxAnalyzerResult
{
    ASTPtr query;

    using Aliases = std::unordered_map<String, ASTPtr>;
    Aliases aliases;

    /// Which column is needed to be ARRAY-JOIN'ed to get the specified.
    /// For example, for `SELECT s.v ... ARRAY JOIN a AS s` will get "s.v" -> "a.v".
    NameToNameMap array_join_result_to_source;

    /// For the ARRAY JOIN section, mapping from the alias to the full column name.
    /// For example, for `ARRAY JOIN [1,2] AS b` "b" -> "array(1,2)" will enter here.
    NameToNameMap array_join_alias_to_name;

    /// The backward mapping for array_join_alias_to_name.
    NameToNameMap array_join_name_to_alias;

    AnalyzedJoin analyzed_join;

    /// Predicate optimizer overrides the sub queries
    bool rewrite_subqueries = false;
};

class SyntaxAnalyzer
{
public:
    SyntaxAnalyzerResult analyze(const ASTPtr & query) const;
};

}
