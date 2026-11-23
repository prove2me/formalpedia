-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.lat_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:31.490459+00:00
-- url     : https://prove2.me/submissions/9699dca4-6bdd-4740-bd30-ebc440c100b0

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply

set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {M : Matrix ι ι K} (h : IsUnit M.det) {A : AddSubgroup (ι → K)} (hA : Lat A) :
    Lat (A.map (mv M)) := by
  have ht : ((A.map (mv M) : AddSubgroup (ι → K)) : Set (ι → K)) =
      (fun v => M⁻¹ *ᵥ v) ⁻¹' (A : Set (ι → K)) := by
    ext v
    simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, mv_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using hu
    · intro hv
      exact ⟨_, hv, by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h]⟩
  have hi : ((A.map (mv M) : AddSubgroup (ι → K)) : Set (ι → K)) =
      (fun v => M *ᵥ v) '' (A : Set (ι → K)) := by
    ext v
    simp [mv_apply]
  constructor
  · rw [ht]
    exact hA.op.preimage (continuous_const.matrix_mulVec continuous_id)
  · rw [hi]
    exact hA.cp.image (continuous_const.matrix_mulVec continuous_id)
end Formalism.FourierDecayAlt.P.A5x5
