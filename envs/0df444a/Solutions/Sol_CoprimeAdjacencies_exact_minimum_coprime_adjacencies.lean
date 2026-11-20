-- Prove2me | solution 1 for CoprimeAdjacencies.exact_minimum_coprime_adjacencies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T20:02:24.650508+00:00
-- url     : https://prove2.me/submissions/c048b9c0-3d92-4360-8a98-9f77a03dd3f0

module
public import Definitions.Def_CoprimeAdjacencies
public import Definitions.Def_CoprimeAdjacencies_Solution
public import Theorems.Thm_P010_P010_exact


set_option autoImplicit true
@[expose] public section
public section
open CoprimeAdjacencies
namespace CoprimeAdjacencies
theorem _root_.solution (n : ℕ) (hn : 4 ≤ n) :
    P010.h n = P010.target n := by
  exact P010.P010_exact n hn
end CoprimeAdjacencies
