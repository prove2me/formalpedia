-- Prove2me | solution 2 for CohnElkies.norm_plusPolynomial_negativeContour_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:40.571773+00:00
-- url     : https://prove2.me/submissions/faff7cc6-58ce-4b93-88aa-6aa7c7181fe3

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


theorem solution
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (s : ℝ) :
    ‖plusPolynomial ε
      (Complex.I *
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
            (ℓ : ℂ))‖ ≤
      27 * (1 + |beta ε|) * (1 + |s|) ^ 3 := by
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hz : Complex.I * (((saddleTaylorContour N : ℂ) + (s : ℂ) * Complex.I) - (ℓ : ℂ)) / (ℓ : ℂ) =
      ((-s / ℓ : ℝ) : ℂ) + Complex.I * (((-saddleNegativeContourOrdinate ℓ N : ℝ) : ℂ)) := by
    unfold saddleNegativeContourOrdinate saddleTaylorContour
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> field_simp <;> push_cast <;> ring
  rw [hz]
  have hN' : 2 * ((N : ℝ) + 1) ≤ ℓ := by push_cast at hN; linarith
  have hℓ1 : 1 ≤ ℓ := by have := (N.cast_nonneg (α := ℝ)); linarith
  have hord : saddleNegativeContourOrdinate ℓ N ≤ 2 := by
    unfold saddleNegativeContourOrdinate
    have : (2 * (N : ℝ) + 1) / ℓ ≤ 1 := by rw [div_le_one hℓ]; linarith
    linarith
  have hord0 : 0 ≤ saddleNegativeContourOrdinate ℓ N := by
    unfold saddleNegativeContourOrdinate; positivity
  set z : ℂ := ((-s / ℓ : ℝ) : ℂ) + Complex.I * (((-saddleNegativeContourOrdinate ℓ N : ℝ) : ℂ)) with hzdef
  have hw : ‖z‖ ≤ |s| + 2 := by
    calc ‖z‖ ≤ ‖((-s / ℓ : ℝ) : ℂ)‖ + ‖Complex.I * (((-saddleNegativeContourOrdinate ℓ N : ℝ) : ℂ))‖ :=
          norm_add_le _ _
      _ = |s| / ℓ + saddleNegativeContourOrdinate ℓ N := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hℓ, abs_neg, abs_of_nonneg hord0]
      _ ≤ |s| + 2 := by
          have : |s| / ℓ ≤ |s| := div_le_self (abs_nonneg s) hℓ1
          linarith
  unfold plusPolynomial
  have hp : ‖1 + z ^ 2 + (beta ε : ℂ) + Complex.I * z * (1 + z ^ 2)‖ ≤
      1 + ‖z‖ ^ 2 + |beta ε| + ‖z‖ * (1 + ‖z‖ ^ 2) := by
    calc ‖1 + z ^ 2 + (beta ε : ℂ) + Complex.I * z * (1 + z ^ 2)‖
        ≤ ‖1 + z ^ 2 + (beta ε : ℂ)‖ + ‖Complex.I * z * (1 + z ^ 2)‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖z ^ 2‖ + ‖(beta ε : ℂ)‖) + ‖z‖ * (‖(1 : ℂ)‖ + ‖z ^ 2‖) := by
          gcongr
          · exact norm_add₃_le
          · rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
            gcongr
            exact norm_add_le _ _
      _ = 1 + ‖z‖ ^ 2 + |beta ε| + ‖z‖ * (1 + ‖z‖ ^ 2) := by
          rw [norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  set w := ‖z‖
  have hw0 : 0 ≤ w := norm_nonneg _
  have hS := abs_nonneg s
  have hb := abs_nonneg (beta ε)
  have h1 : 1 + w + w ^ 2 + w ^ 3 ≤ 27 * (1 + |s|) ^ 3 := by
    have : 1 + w + w ^ 2 + w ^ 3 ≤ (1 + w) ^ 3 := by nlinarith [pow_nonneg hw0 2]
    have h3 : (1 + w) ^ 3 ≤ (3 * (1 + |s|)) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    nlinarith
  have h2 : 1 ≤ (1 + |s|) ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

