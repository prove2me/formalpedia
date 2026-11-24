-- Prove2me | solution 1 for FFactor.sum_split3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:51.549728+00:00
-- url     : https://prove2.me/submissions/b190112d-f360-4a76-8d65-848f9ac43858

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace FFactor
theorem _root_.solution {S T : Finset V} (hST : Disjoint S T) (F : V → ℤ) :
    ∑ u, F u = ∑ u ∈ S, F u + ∑ u ∈ T, F u + ∑ u ∈ univ \ (S ∪ T), F u := by
  rw [← sum_union hST, ← sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ _)]
end FFactor
