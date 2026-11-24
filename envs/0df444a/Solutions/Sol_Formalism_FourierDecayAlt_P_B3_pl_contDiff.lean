-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:30:13.754191+00:00
-- url     : https://prove2.me/submissions/804062fc-7355-4e87-b4c2-1417aa07c208

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
theorem _root_.solution (a b k : ℝ) : ContDiff ℝ 2 (pl a b k) := by
  unfold pl
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
end Formalism.FourierDecayAlt.P.B3
