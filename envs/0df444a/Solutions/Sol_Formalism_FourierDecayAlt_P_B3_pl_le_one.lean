-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:57:12.014559+00:00
-- url     : https://prove2.me/submissions/be0350e6-94bd-4309-b213-1338121adba3

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
theorem _root_.solution (a b k x : ℝ) : pl a b k x ≤ 1 := by
  unfold pl
  nlinarith [Real.smoothTransition.nonneg (k * (x - a)), Real.smoothTransition.nonneg (k * (b - x)),
    Real.smoothTransition.le_one (k * (x - a)), Real.smoothTransition.le_one (k * (b - x))]
end Formalism.FourierDecayAlt.P.B3
