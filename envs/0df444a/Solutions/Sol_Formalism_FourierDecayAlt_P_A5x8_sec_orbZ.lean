-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_orbZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:45.495204+00:00
-- url     : https://prove2.me/submissions/5670c115-c895-4771-888a-e348b4828390

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_upJ_m
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K]
variable {m N : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) (p : lowW K h.1 h.2 × upUniG K h.1.sum)
    (ξ η : Fin h.1.sum → K) :
    orbZ (addBlock h 1 c) (sec_lowJ h c p.1 ξ, sec_upJ h c p.2 η) =
      bigZ (addBlock_sum h c) (orbZ h p) ξ η (c : K) := by
  unfold orbZ bigZ
  change sec_m (sec_lowJ h c p.1 ξ) * _ * sec_m (sec_upJ h c p.2 η) = _
  rw [sec_lowJ_m, sec_upJ_m, sec_pt, blkM_mul, blkM_mul]
  congr 1
  · simp
  · simp [Matrix.mulVec_mulVec]
  · simp [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  · simp [Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.A5x8
