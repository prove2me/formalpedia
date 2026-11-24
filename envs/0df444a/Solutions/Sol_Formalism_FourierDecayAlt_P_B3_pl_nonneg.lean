-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:24.850653+00:00
-- url     : https://prove2.me/submissions/cb6222db-748e-4b6a-a31a-17890948b2c5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution (a b k x : ℝ) : 0 ≤ pl a b k x := by
  unfold pl
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
end Formalism.FourierDecayAlt.P.B3
