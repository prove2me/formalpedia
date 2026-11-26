-- Prove2me | solution 1 for FirstPassageLinearTransport.fair_three_word_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:52.133231+00:00
-- url     : https://prove2.me/submissions/b6b916ed-9751-46e3-a036-2d0509262daf

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_collatzTiltLambda_pos
import Theorems.Thm_FirstPassageLinearTransport_fair_bernoulliWordWeight_change

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {a b : ℕ} {center : ℝ}
    (u : Fin a → Bool) (v : Fin b → Bool) (w : Fin a → Bool)
    (hterminal : center ≤
      wordIncrementSum collatzLogIncrement u +
        wordIncrementSum collatzLogIncrement v +
        wordIncrementSum collatzLogIncrement w) :
    bernoulliWordWeight (1 / 2) u *
        bernoulliWordWeight (1 / 2) v *
        bernoulliWordWeight (1 / 2) w ≤
      (bernoulliWordWeight collatzTilt u *
        bernoulliWordWeight collatzTilt v *
        bernoulliWordWeight collatzTilt w) *
      Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * center) := by
  have htilt : 0 ≤
      bernoulliWordWeight collatzTilt u *
        bernoulliWordWeight collatzTilt v *
        bernoulliWordWeight collatzTilt w := by
    exact mul_nonneg
      (mul_nonneg
        (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le u)
        (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le v))
      (bernoulliWordWeight_nonneg collatzTilt_pos.le collatzTilt_lt_one.le w)
  have hexp :
      -(collatzFairTiltRate * (a : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement u +
        (-(collatzFairTiltRate * (b : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) +
        (-(collatzFairTiltRate * (a : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement w) ≤
      -(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
        collatzTiltLambda * center := by
    have hmul := mul_le_mul_of_nonneg_left hterminal collatzTiltLambda_pos.le
    push_cast
    linarith
  rw [fair_bernoulliWordWeight_change u,
    fair_bernoulliWordWeight_change v,
    fair_bernoulliWordWeight_change w]
  calc
    _ = (bernoulliWordWeight collatzTilt u *
          bernoulliWordWeight collatzTilt v *
          bernoulliWordWeight collatzTilt w) *
        Real.exp (
          (-(collatzFairTiltRate * (a : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement u) +
          (-(collatzFairTiltRate * (b : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement v) +
          (-(collatzFairTiltRate * (a : ℝ)) -
            collatzTiltLambda * wordIncrementSum collatzLogIncrement w)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) htilt
end FirstPassageLinearTransport
