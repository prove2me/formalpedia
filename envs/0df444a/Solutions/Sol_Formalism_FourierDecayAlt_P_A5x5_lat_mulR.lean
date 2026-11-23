-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.lat_mulR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:30.379869+00:00
-- url     : https://prove2.me/submissions/f670a637-a63e-4065-846a-5744a380332c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
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



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) (x : Kˣ) :
    Lat (mulR R (x : K)) := by
  constructor
  · have h : ((mulR R (x : K)) : Set K) = (fun y => ((x⁻¹ : Kˣ) : K) * y) ⁻¹' (R : Set K) := by
      ext y
      simp only [mulR, AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.coe_mulLeft, Subring.coe_toAddSubgroup]
      constructor
      · rintro ⟨r, hr, rfl⟩
        simpa using hr
      · intro hy
        exact ⟨_, hy, by simp⟩
    rw [h]
    exact ho.preimage (continuous_mul_left _)
  · have h : ((mulR R (x : K)) : Set K) = (fun y => (x : K) * y) '' (R : Set K) := by
      ext y
      simp [mulR]
    rw [h]
    exact hc.image (continuous_mul_left _)
end Formalism.FourierDecayAlt.P.A5x5
