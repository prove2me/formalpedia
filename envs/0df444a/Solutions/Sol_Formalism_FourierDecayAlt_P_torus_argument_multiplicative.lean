-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.torus_argument_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:14.759887+00:00
-- url     : https://prove2.me/submissions/6ed96f6d-126a-4631-8f83-0e201ede714e

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.TaArgMul := by
  intro a b Dr ζ hDr hζ
  have h := Complex.arg_mul_coe_angle hDr hζ
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  have e : Complex.arg (Dr * ζ) = Complex.arg Dr + Complex.arg ζ + 2 * Real.pi * m := by linarith
  unfold C7.taS
  rw [← Complex.exp_add, e, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(m * (a + b)), ?_⟩
  push_cast; ring
end Formalism.FourierDecayAlt.P
