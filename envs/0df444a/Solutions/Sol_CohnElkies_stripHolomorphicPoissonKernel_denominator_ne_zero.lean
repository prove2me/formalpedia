-- Prove2me | solution 1 for CohnElkies.stripHolomorphicPoissonKernel_denominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/f715737e-0e4c-452f-9221-5128eebf6a1a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Complex.exp
      (((Real.pi : ℂ) *
        (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
          (2 * (ℓ : ℂ))) - 1 ≠ 0 := by
  change -ℓ < z.im ∧ z.im < ℓ at hz
  have hargument :
      (((Real.pi : ℂ) *
        (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
          (2 * (ℓ : ℂ))).im =
        Real.pi * (z.im + ℓ) / (2 * ℓ) := by
    rw [show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_im]
    simp [Complex.mul_im]
  have hpositive : 0 < Real.pi * (z.im + ℓ) / (2 * ℓ) := by
    exact div_pos (mul_pos Real.pi_pos (by linarith))
      (mul_pos (by norm_num) hℓ)
  have hless : Real.pi * (z.im + ℓ) / (2 * ℓ) < Real.pi := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hℓ)).2
    nlinarith [mul_pos Real.pi_pos (show 0 < ℓ - z.im by linarith)]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hpositive hless
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.one_im, sub_zero,
    Complex.exp_im, hargument] at him
  exact (mul_pos (Real.exp_pos _) hsin).ne' him
end CohnElkies
