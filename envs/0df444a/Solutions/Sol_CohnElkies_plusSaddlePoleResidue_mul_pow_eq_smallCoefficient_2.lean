-- Prove2me | solution 2 for CohnElkies.plusSaddlePoleResidue_mul_pow_eq_smallCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:56:24.363432+00:00
-- url     : https://prove2.me/submissions/37074d46-e6f2-4bef-ab74-6ff50af4e061

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
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (r : ℝ) :
    plusSaddlePoleResidue ε ℓ n *
        ((r ^ (2 * n) : ℝ) : ℂ) =
      ((saddleOriginValue ε ℓ *
        ((-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ)) *
        plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hβ : beta ε ≠ 0 := (beta_pos hε).ne'
  have harg : Complex.I * (-(((2 * n : ℕ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ) =
      -(Complex.I * (((1 + 2 * (n : ℝ) / ℓ : ℝ)) : ℂ)) := by
    push_cast
    field_simp
    ring
  have harg2 : -(Complex.I * (((1 + 2 * (n : ℝ) / ℓ : ℝ)) : ℂ)) =
      Complex.I * ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ) := by push_cast; ring
  have hexp1 : Complex.exp (((ℓ : ℂ) - -(((2 * n : ℕ) : ℂ))) * (Real.log Real.pi : ℂ) / 2) =
      ((Real.exp ((ℓ + 2 * n) * Real.log Real.pi / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hexp2 : Complex.exp ((ℓ : ℂ) * (realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ) : ℂ)) =
      ((Real.exp (ℓ * realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  unfold plusSaddlePoleResidue plusSaddleRegularMellinFactor saddleRegularMellinFactor
  rw [harg, mellinShellPhase_neg, mellinShellPhase_imaginary, harg2, plusPolynomial_imaginary, hexp1, hexp2]
  have e1 : Real.exp ((ℓ + 2 * n) * Real.log Real.pi / 2) = Real.pi ^ (ℓ / 2) * Real.pi ^ n := by
    rw [Real.rpow_def_of_pos Real.pi_pos,
      show (Real.pi : ℝ) ^ n = Real.exp (Real.log Real.pi) ^ n by rw [Real.exp_log Real.pi_pos],
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  have e2 : Real.exp (ℓ * (realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ) - realHyperbolicShellPhase ε 1) -
      2 * (n : ℝ) * saddleShellDerivativeOne ε) =
      Real.exp (ℓ * realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ)) /
        Real.exp (ℓ * realHyperbolicShellPhase ε 1) / Real.exp (2 * saddleShellDerivativeOne ε) ^ n := by
    rw [show ℓ * (realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ) - realHyperbolicShellPhase ε 1) -
      2 * (n : ℝ) * saddleShellDerivativeOne ε = ℓ * realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ) -
        ℓ * realHyperbolicShellPhase ε 1 - n * (2 * saddleShellDerivativeOne ε) by ring,
      Real.exp_sub, Real.exp_sub, Real.exp_nat_mul]
  have key : (2 : ℝ) * (-1) ^ n / (n.factorial : ℝ) *
      (Real.exp ((ℓ + 2 * n) * Real.log Real.pi / 2) *
        Real.exp (ℓ * realHyperbolicShellPhase ε (1 + 2 * (n : ℝ) / ℓ)) *
        (beta ε + (1 - -(1 + 2 * (n : ℝ) / ℓ)) ^ 2 * (1 + -(1 + 2 * (n : ℝ) / ℓ)))) * r ^ (2 * n) =
      saddleOriginValue ε ℓ * ((-saddleSmallRadiusVariable ε r) ^ n / (n.factorial : ℝ)) *
        plusSaddleSmallRadiusCoefficient ε ℓ n := by
    unfold saddleOriginValue saddleSmallRadiusVariable plusSaddleSmallRadiusCoefficient
    rw [e1, e2, neg_pow (Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) * r ^ 2), mul_pow, mul_pow, pow_mul]
    have h1 := Real.exp_pos (ℓ * realHyperbolicShellPhase ε 1)
    have h2 := Real.exp_pos (2 * saddleShellDerivativeOne ε)
    have h3 : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← key]
  push_cast
  ring

