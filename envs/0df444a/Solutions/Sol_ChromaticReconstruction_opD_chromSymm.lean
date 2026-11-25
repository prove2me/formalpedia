-- Prove2me | solution 1 for ChromaticReconstruction.opD_chromSymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:42.888977+00:00
-- url     : https://prove2.me/submissions/52aec704-a0f3-4c36-8382-cb2e8d0f1995

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_opD_pre
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
    opD q N (chromSymm G) = ∑ F ∈ G.edgeFinset.powerset, (-1) ^ F.card * innerSum q F := by
  unfold opD
  rw [opD_pre q N G hN, map_sum]
  refine sum_congr rfl fun F _ => ?_
  rw [map_mul, algHom_C, map_sum, innerSum, mul_sum, mul_sum]
  refine sum_congr rfl fun C0 _ => ?_
  rw [map_mul, algHom_C, smul_eq_C_mul]
  simp
end ChromaticReconstruction
