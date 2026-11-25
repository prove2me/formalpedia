-- Prove2me | solution 1 for ChromaticReconstruction.opD_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:22.874182+00:00
-- url     : https://prove2.me/submissions/e9b474f4-6436-4ea4-ada5-4bfc2fa1cd87

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_pderiv_typeMonomial
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (q N : ℕ) (G : SimpleGraph V) (hN : Fintype.card V < N) :
    ∑ r ∈ range N, C (r : ℚ) * X (q * r - 1) * psiQ q (pderiv r (chromSymm G)) =
      ∑ F ∈ G.edgeFinset.powerset, C ((-1) ^ F.card) * ∑ C0 ∈ compSets (F : Set (Sym2 V)),
        C (C0.card : ℚ) * (X (q * C0.card - 1) *
          ∏ C ∈ (compSets (F : Set (Sym2 V))).erase C0, X (q * C.card)) := by
  unfold chromSymm
  have hc : ∀ n : ℕ, ((-1 : MvPolynomial ℕ ℚ) ^ n) = C ((-1) ^ n) := by simp
  simp only [hc, map_sum, pderiv_C_mul, pderiv_typeMonomial, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun F _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun C0 _ => ?_
  have hmem : C0.card ∈ range N := mem_range.2 (lt_of_le_of_lt (card_le_univ C0) hN)
  rw [sum_congr rfl (fun x _ => by rw [mul_ite, mul_zero, apply_ite (psiQ q), map_zero,
    mul_ite, mul_zero])]
  rw [sum_ite_eq, if_pos hmem]
  simp only [psiQ, map_mul, rename_C, map_prod, rename_X]
  ring
end ChromaticReconstruction
