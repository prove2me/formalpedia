-- Prove2me | solution 1 for EdmondsPolytope.edmonds_matching_polytope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:36.863493+00:00
-- url     : https://prove2.me/submissions/4bf51c4b-2f6d-4a82-a8c7-9b0f073e72e8

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
public import Definitions.Def_MatchingPolytope_Matching
public import Definitions.Def_EdmondsPolytope_Solution
public import Theorems.Thm_MatchingPolytope_edmonds_matching_polytope


set_option autoImplicit true
@[expose] public section
public section
open EdmondsPolytope
namespace EdmondsPolytope
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    convexHull ℝ (matchingVectors G) = matchingPolytope G :=
  MatchingPolytope.edmonds_matching_polytope G
end EdmondsPolytope
