-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:47:51.449476+00:00
-- url     : https://prove2.me/submissions/d5d531c2-45c7-46d7-ae69-60bd5326b1bb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_jump_increment_integrated_uniform_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open AvramDividend.Classical

/-! The C1 finite-band approximation error is first-moment weighted.
Outside the band its cost is controlled by the same residual first moment. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (f : ℝ → ℝ) (hf : Continuous f)
    (y R M ε L : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hDerBound : ∀ z : ℝ, |deriv w z| ≤ L)
    (hfBound : ∀ r : ℝ, 0 ≤ r → |f r| ≤ L + ε)
    (happrox : ∀ r ∈ Icc (0 : ℝ) M,
      |deriv w (y - r) - f r| ≤ ε) :
    |(w y - w (y - R)) - (∫ r in (0 : ℝ)..R, f r)| ≤
      ε * R + (2 * L + ε) * (if M < R then R else 0) := by
  by_cases hlarge : M < R
  · have hglob : ∀ r ∈ uIoc (0 : ℝ) R,
        |deriv w (y - r) - f r| ≤ 2 * L + ε := by
      intro r hr
      have hr' : r ∈ Ioc (0 : ℝ) R := by
        simpa [uIoc_of_le hR] using hr
      calc
        |deriv w (y - r) - f r| ≤ |deriv w (y - r)| + |f r| :=
          abs_sub _ _
        _ ≤ L + (L + ε) :=
          add_le_add (hDerBound _) (hfBound r hr'.1.le)
        _ = 2 * L + ε := by ring
    have hbound :=
      avram_wave5_04c_C1_jump_increment_integrated_uniform_error
        w hwC1 f hf y R (2 * L + ε) hR hglob
    simp only [if_pos hlarge]
    nlinarith [mul_nonneg hε hR]
  · have hRle : R ≤ M := le_of_not_gt hlarge
    have hloc : ∀ r ∈ uIoc (0 : ℝ) R,
        |deriv w (y - r) - f r| ≤ ε := by
      intro r hr
      have hr' : r ∈ Ioc (0 : ℝ) R := by
        simpa [uIoc_of_le hR] using hr
      exact happrox r ⟨hr'.1.le, le_trans hr'.2 hRle⟩
    have hbound :=
      avram_wave5_04c_C1_jump_increment_integrated_uniform_error
        w hwC1 f hf y R ε hR hloc
    simpa [if_neg hlarge] using hbound
