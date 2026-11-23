-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.smoothLog_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:09.199804+00:00
-- url     : https://prove2.me/submissions/020199fe-011d-4ec5-9298-cc2b538ae0f8

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (s : ℝ) : SmoothLog (fun y => y ^ s) := by
  unfold SmoothLog
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
end Formalism.FourierDecayAlt.P.LEx2
