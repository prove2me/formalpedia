-- Prove2me | solution 1 for ErdosGirth.expected_indep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:10.167035+00:00
-- url     : https://prove2.me/submissions/7dd39950-3b5c-409b-b72c-eadb95959f99

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_sum_wt_disjoint
public import Theorems.Thm_ErdosGirth_edgesIn_subset_pairs

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} (t : ℕ) (p : ℝ) :
    ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S = m.choose t * (1 - p) ^ t.choose 2 := by
  calc ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S
      = ∑ S ∈ (pairs m).powerset, ∑ T ∈ powersetCard t (univ : Finset (Fin m)),
          (if Disjoint (edgesIn T) S then wt m p S else 0) := by
        simp_rw [indep, mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ T ∈ powersetCard t (univ : Finset (Fin m)), ∑ S ∈ (pairs m).powerset,
          (if Disjoint (edgesIn T) S then wt m p S else 0) := sum_comm
    _ = ∑ T ∈ powersetCard t (univ : Finset (Fin m)), (1 - p) ^ t.choose 2 := by
        refine sum_congr rfl fun T hT => ?_
        rw [sum_wt_disjoint p (edgesIn_subset_pairs T), edgesIn, Sym2.card_image_offDiag,
          (mem_powersetCard.mp hT).2]
    _ = m.choose t * (1 - p) ^ t.choose 2 := by
        rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
end ErdosGirth
