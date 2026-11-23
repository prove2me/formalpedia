-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.weighted_L2_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:15.048279+00:00
-- url     : https://prove2.me/submissions/04df7f8b-2a59-4c12-9b2f-dcb1dcea15cb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (a : ℂ) (f : B.Ω → ℂ) (hf : WeightedL2 B wt f) :
    WeightedL2 B wt (fun ω => a * f ω) := by
  unfold WeightedL2 at *
  obtain ⟨hm, hi⟩ := hf
  refine ⟨hm.const_mul a, ?_⟩
  refine (hi.const_mul (‖a‖ ^ 2)).congr (ae_of_all _ fun ω => ?_)
  simp only [norm_mul, mul_pow]
  ring
end Formalism.FourierDecayAlt.P.LEx1
