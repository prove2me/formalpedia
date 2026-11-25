-- Prove2me | solution 1 for DegreeSequences.egReduce_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:58:43.419181+00:00
-- url     : https://prove2.me/submissions/e79a98f2-b3da-4444-9164-19ab82409b01

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_egReduce_add

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (F : Finset (Fin n)) :
    ∑ i ∈ F, d i = ∑ i ∈ F, egReduce d t p i + (if t ∈ F then 1 else 0) +
      (if p ∈ F then 1 else 0) := by
  rw [Finset.sum_congr rfl fun i _ => egReduce_add d t p htp ht hp i, sum_add_distrib,
    sum_add_distrib, sum_ite_eq', sum_ite_eq']
end DegreeSequences
