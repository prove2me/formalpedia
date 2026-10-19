-- Prove2me | solution 2 for CohnElkies.plusSaddlePoleResidue_explicit_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:45.821117+00:00
-- url     : https://prove2.me/submissions/bef60d8a-b811-4e22-871c-661b8c0167a7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddlePoleResidue ε ℓ n =
      ((2 * (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        (Real.pi ^ (ℓ / 2 + (n : ℝ)) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (1 + 2 * (n : ℝ) / ℓ))) *
        (beta ε - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) : ℝ) : ℂ) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hℓ0 : (ℓ:ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have harg : Complex.I * (-((2 * n : ℕ) : ℂ) - (ℓ : ℂ)) / (ℓ : ℂ) =
      -(Complex.I * (((1 + 2 * (n:ℝ) / ℓ : ℝ)) : ℂ)) := by
    push_cast; field_simp; ring
  have hP : plusPolynomial ε (-(Complex.I * (((1 + 2 * (n:ℝ) / ℓ : ℝ)) : ℂ))) =
      ((beta ε - (2 * (n:ℝ) / ℓ) * (2 + 2 * (n:ℝ) / ℓ) ^ 2 : ℝ) : ℂ) := by
    unfold plusPolynomial
    push_cast
    linear_combination ((1 + 2 * (n:ℂ) / (ℓ:ℂ)) ^ 2 - (1 + 2 * (n:ℂ) / (ℓ:ℂ)) -
      (Complex.I ^ 2 - 1) * (1 + 2 * (n:ℂ) / (ℓ:ℂ)) ^ 3) * hI
  have hE : Complex.exp (((ℓ:ℂ) - -((2 * n : ℕ) : ℂ)) * (Real.log Real.pi : ℂ) / 2) =
      ((Real.pi ^ (ℓ / 2 + (n:ℝ)) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold plusSaddlePoleResidue plusSaddleRegularMellinFactor saddleRegularMellinFactor
  rw [harg, mellinShellPhase_neg, mellinShellPhase_imaginary, hP, hE]
  push_cast
  ring

