-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.blk_app
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:22.992074+00:00
-- url     : https://prove2.me/submissions/c0b29787-21f7-4cdf-94bf-e2dc2f75a90a

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
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (l : List ℕ) (s : ℕ) (hs : 1 ≤ s) : blk (l ++ [s]) l.sum = l.length := by
  induction l with
  | nil => simp [blk]; omega
  | cons a l ih => simp [blk, ih]; omega
end Formalism.FourierDecayAlt.P.A5x2
