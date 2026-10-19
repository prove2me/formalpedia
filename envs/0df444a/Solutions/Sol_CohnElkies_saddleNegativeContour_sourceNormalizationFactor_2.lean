-- Prove2me | solution 2 for CohnElkies.saddleNegativeContour_sourceNormalizationFactor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:53.063457+00:00
-- url     : https://prove2.me/submissions/76f218cb-fa61-4ecd-8d54-a8baa8052a2e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
theorem h47_srcnorm (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) *
      Real.exp ((ℓ - saddleTaylorContour N) * Real.log Real.pi / 2) *
      Real.exp (ℓ * realHyperbolicShellPhase ε (saddleNegativeContourOrdinate ℓ N)) /
      (Real.exp ((ℓ / 2) * Real.log Real.pi) * Real.exp (ℓ * realHyperbolicShellPhase ε 1)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) * saddleSmallRadiusVariable ε r ^ N *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have key : ∀ (x a1 a2 a3 a4 e pe : ℝ), a1 + a2 - (a3 + a4) = e + ((2 * N : ℕ) : ℝ) * e + pe →
      x ^ (2 * N + 1) * Real.exp a1 * Real.exp a2 / (Real.exp a3 * Real.exp a4) =
        Real.exp e * x * (Real.exp e * x) ^ (2 * N) * Real.exp pe := by
    intro x a1 a2 a3 a4 e pe h
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_add a3 a4, div_eq_mul_inv, ← Real.exp_neg]
    have h2 : Real.exp a1 * Real.exp a2 * Real.exp (-(a3 + a4)) =
        Real.exp e * Real.exp (((2 * N : ℕ) : ℝ) * e) * Real.exp pe := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1 <;> linarith
    calc _ = x ^ (2 * N + 1) * (Real.exp a1 * Real.exp a2 * Real.exp (-(a3 + a4))) := by ring
      _ = _ := by rw [h2]; ring
  have hV : saddleSmallRadiusVariable ε r =
      (Real.exp (Real.log Real.pi / 2 + saddleShellDerivativeOne ε) * r) ^ 2 := by
    unfold saddleSmallRadiusVariable
    rw [mul_pow, ← Real.exp_nat_mul, show ((2:ℕ):ℝ) * (Real.log Real.pi / 2 + saddleShellDerivativeOne ε)
      = Real.log Real.pi + 2 * saddleShellDerivativeOne ε by push_cast; ring, Real.exp_add,
      Real.exp_log Real.pi_pos]
  rw [hV, Real.sqrt_sq (mul_nonneg (Real.exp_pos _).le hr), ← pow_mul]
  apply key
  unfold saddleNegativeContourPhaseError saddleTaylorContour
  push_cast
  ring

theorem solution
    (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) *
      Real.exp
        ((ℓ - saddleTaylorContour N) *
          Real.log Real.pi / 2) *
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) /
      (Real.exp ((ℓ / 2) * Real.log Real.pi) *
        Real.exp (ℓ * realHyperbolicShellPhase ε 1)) =
      Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N *
          Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  exact h47_srcnorm ε ℓ N hr

