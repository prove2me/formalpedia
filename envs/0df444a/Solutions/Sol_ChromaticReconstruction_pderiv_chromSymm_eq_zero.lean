-- Prove2me | solution 1 for ChromaticReconstruction.pderiv_chromSymm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:44.616077+00:00
-- url     : https://prove2.me/submissions/c2b6bd3e-677a-48a8-814c-7bb9b89f970b

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_nonempty_of_mem_compSets
import Theorems.Thm_ChromaticReconstruction_pderiv_typeMonomial
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
theorem _root_.solution (G : SimpleGraph V) (r : ℕ) (hr : r = 0 ∨ Fintype.card V < r) :
    pderiv r (chromSymm G) = 0 := by
  unfold chromSymm
  rw [map_sum]
  apply sum_eq_zero
  intro A _
  have hc : ((-1 : MvPolynomial ℕ ℚ) ^ A.card) = C ((-1) ^ A.card) := by simp
  rw [hc, pderiv_C_mul, pderiv_typeMonomial, sum_eq_zero, mul_zero]
  intro C0 hC0
  rw [if_neg]
  have h1 := (nonempty_of_mem_compSets hC0).card_pos
  have h2 := card_le_univ C0
  omega
end ChromaticReconstruction
