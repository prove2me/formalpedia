-- Prove2me | solution 1 for ChromaticReconstruction.phi_uniformLeafExt_eq_opD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:41:30.020558+00:00
-- url     : https://prove2.me/submissions/1e11023a-7992-4f7f-a8c8-764562241636

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Theorems.Thm_ChromaticReconstruction_phi_uniformLeafExt_eq
import Theorems.Thm_ChromaticReconstruction_opD_chromSymm
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
theorem _root_.solution (q N : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V)
    (hN : Fintype.card V < N) :
    phi (uniformLeafExt q G) =
      ((-1) ^ ((q - 1) * Fintype.card V - 1) * ((q - 1 : ℕ) : ℚ)) • opD q N (chromSymm G) := by
  rw [phi_uniformLeafExt_eq q hq G, opD_chromSymm q N G hN, smul_sum]
  refine sum_congr rfl fun F _ => ?_
  rw [smul_eq_C_mul, smul_eq_C_mul, pow_add]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring
end ChromaticReconstruction
