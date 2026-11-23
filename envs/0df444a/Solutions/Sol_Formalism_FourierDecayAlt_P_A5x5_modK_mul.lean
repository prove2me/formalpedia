-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.modK_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:42.63782+00:00
-- url     : https://prove2.me/submissions/0c158873-cb26-4128-8505-00a8f7d619ff

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_gi_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_mulR
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
theorem _root_.solution (ho : IsOpen (R : Set K)) (hc : IsCompact (R : Set K)) (x y : Kˣ) :
    modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K) := by
  have hf : Function.Injective (AddMonoidHom.mulLeft (x : K)) := fun a b h =>
    (Units.mul_right_inj x).mp h
  have e1 : (mulR R (y : K)).map (AddMonoidHom.mulLeft (x : K)) = mulR R ((x : K) * (y : K)) := by
    ext z
    simp [mulR, mul_assoc]
  have h1 := gi_trans (lat_mulR ho hc (x * y)) (lat_mulR ho hc x) (lat_R ho hc)
  rw [Units.val_mul] at h1
  have h2 : gi (mulR R ((x : K) * (y : K))) (mulR R (x : K)) = gi (mulR R (y : K)) R.toAddSubgroup := by
    rw [← e1, show mulR R (x : K) = R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : K)) from rfl,
      gi_map hf]
  simp only [modK_eq]
  rw [← h1, h2, mul_comm]
end Formalism.FourierDecayAlt.P.A5x5
