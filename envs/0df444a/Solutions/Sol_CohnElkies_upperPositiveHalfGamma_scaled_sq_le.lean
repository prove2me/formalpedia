-- Prove2me | solution 1 for CohnElkies.upperPositiveHalfGamma_scaled_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/dbb27195-cfa0-4006-859d-3bbf0dbf3c84

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_norm_gamma_half_add_imaginary_sq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (n : ℕ) (x : ℝ) :
    Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 ≤
      ‖Complex.Gamma
        (((((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          Complex.I * (x : ℂ))‖ ^ 2 *
        Real.cosh (Real.pi * x) := by
  induction n with
  | zero =>
      norm_num only [Nat.cast_zero, zero_add]
      have hhalf :
          ‖Complex.Gamma
            (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
            Real.pi / Real.cosh (Real.pi * x) := by
        convert! norm_gamma_half_add_imaginary_sq x using 1; norm_num
      rw [hhalf, Real.Gamma_one_half_eq,
        Real.sq_sqrt Real.pi_pos.le]
      field_simp [(Real.cosh_pos (Real.pi * x)).ne']; norm_num
  | succ n ih =>
      let q : ℝ := (n : ℝ) + 1 / 2
      have hq : 0 < q := by
        try dsimp [q]
        positivity
      have hreal :
          Real.Gamma (((n + 1 : ℕ) : ℝ) + 1 / 2) =
            q * Real.Gamma q := by
        convert! Real.Gamma_add_one hq.ne' using 1
        · simp [q, Nat.cast_add, Nat.cast_one]
          ring_nf
      let z : ℂ := (q : ℂ) + Complex.I * (x : ℂ)
      have hz : z ≠ 0 := by
        intro hzero
        have h := congrArg Complex.re hzero
        have hqzero : q = 0 := by simpa [z] using! h
        exact hq.ne' hqzero
      have hcomplex :
          Complex.Gamma
              (((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) +
                Complex.I * (x : ℂ)) =
            z * Complex.Gamma z := by
        convert! Complex.Gamma_add_one z hz using 1
        · simp [z, q, Nat.cast_add, Nat.cast_one]
          ring_nf
      have hzlower : q ≤ ‖z‖ := by
        have h := Complex.abs_re_le_norm z
        simpa [z, abs_of_pos hq] using! h
      have hcosh : 0 ≤ Real.cosh (Real.pi * x) :=
        (Real.cosh_pos _).le
      have hqnorm : 0 ≤ ‖Complex.Gamma z‖ ^ 2 :=
        sq_nonneg _
      rw [hreal, hcomplex, norm_mul]
      have ih' :
          Real.Gamma q ^ 2 ≤
            ‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x) := by
        simpa [q, z] using! ih
      calc
        (q * Real.Gamma q) ^ 2 =
            q ^ 2 * Real.Gamma q ^ 2 := by ring
        _ ≤ q ^ 2 *
            (‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x)) :=
          mul_le_mul_of_nonneg_left ih' (sq_nonneg q)
        _ ≤ ‖z‖ ^ 2 *
            (‖Complex.Gamma z‖ ^ 2 *
              Real.cosh (Real.pi * x)) := by
          gcongr
        _ = (‖z‖ * ‖Complex.Gamma z‖) ^ 2 *
            Real.cosh (Real.pi * x) := by ring
end CohnElkies
