-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.hasFDerivAt_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:53.456843+00:00
-- url     : https://prove2.me/submissions/000f5426-147e-4877-b368-a04fed98e37b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution {u : ℂ → ℂ} {ζ : ℂ} (hd : DifferentiableAt ℝ u ζ) :
    HasFDerivAt (fun w => star (u w)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ u ζ)) ζ := by
  refine hd.hasFDerivAt.star.congr_fderiv ?_
  exact ContinuousLinearMap.ext fun v => rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
