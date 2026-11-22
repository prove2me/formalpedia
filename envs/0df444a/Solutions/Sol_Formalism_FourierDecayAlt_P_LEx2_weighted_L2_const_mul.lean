-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.weighted_L2_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:39.189674+00:00
-- url     : https://prove2.me/submissions/e2049dfb-374c-4fa9-9fc4-b700cd555c55

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

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
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (a : ℂ) (f : B.Ω → ℂ) (hf : WeightedL2 B wt f) :
    WeightedL2 B wt (fun ω => a * f ω) := by
  refine ⟨hf.1.const_mul a, ?_⟩
  have : (fun ω => wt ω * ‖a * f ω‖ ^ 2) = fun ω => ‖a‖ ^ 2 * (wt ω * ‖f ω‖ ^ 2) := by
    funext ω; rw [norm_mul]; ring
  rw [this]; exact hf.2.const_mul _
end Formalism.FourierDecayAlt.P.LEx2
