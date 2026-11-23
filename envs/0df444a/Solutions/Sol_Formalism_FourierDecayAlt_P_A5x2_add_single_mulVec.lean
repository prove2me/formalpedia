-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.add_single_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:06.403176+00:00
-- url     : https://prove2.me/submissions/6949f235-316e-45b8-a8cc-9723e75df0df

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
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (m y : Fin n → K) (c : Fin n) :
    (Z + vecMulVec m (Pi.single c 1)) *ᵥ y = Z *ᵥ y + y c • m := by
  rw [Matrix.add_mulVec]
  congr 1
  ext a
  simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.single_apply, mul_comm]
end Formalism.FourierDecayAlt.P.A5x2
