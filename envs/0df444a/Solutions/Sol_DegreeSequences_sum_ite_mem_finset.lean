-- Prove2me | solution 1 for DegreeSequences.sum_ite_mem_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:07:50.171803+00:00
-- url     : https://prove2.me/submissions/457983fa-90bc-4097-a6e2-63f8e4ad6981

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_sum_ite_sym2_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (v : V) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, ¬ e.IsDiag) :
    (∑ w, if s(v, w) ∈ R then 1 else 0) = ∑ e ∈ R, if v ∈ e then 1 else 0 := by
  have : ∀ w, (if s(v, w) ∈ R then 1 else 0) = ∑ e ∈ R, if s(v, w) = e then 1 else 0 := by
    intro w
    rw [Finset.sum_ite_eq]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => sum_ite_sym2_eq v e (hR e he)
end DegreeSequences
