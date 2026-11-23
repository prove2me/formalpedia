-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.colOp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:32.404004+00:00
-- url     : https://prove2.me/submissions/34d42c14-9af4-4c1b-a1c0-f35ad1b57dcb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (ξ : Fin n → K) (c : Fin n) (hξ : ξ c = 0) :
    (1 + vecMulVec ξ (Pi.single c 1)) * (1 - vecMulVec ξ (Pi.single c 1)) = 1 := by
  have : vecMulVec ξ (Pi.single c (1:K)) * vecMulVec ξ (Pi.single c 1) = 0 := by
    ext a b
    simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, hξ]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, this]; simp
end Formalism.FourierDecayAlt.P.A5x2
