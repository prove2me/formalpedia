-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:06:22.78604+00:00
-- url     : https://prove2.me/submissions/c98a960a-233c-4a85-b916-10a71d5e0717

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
open AvramDividend.Classical

/-! Fixed polynomial and moving-base robust first-moment domination of
the C1 negative jump primitive, without any second derivatives. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ b R : ℝ, |b - x| < δ → 0 ≤ R →
        |(w b - w (b - R)) -
          (∫ r in (0 : ℝ)..R,
            Polynomial.eval (Real.exp (-r)) p)| ≤
          ε * R + (2 * L + ε) * (if M < R then R else 0) := by
  obtain ⟨δ, hδ, p, hp0, hpApprox, hpBound⟩ :=
    avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
      w hwC1 L hL hLip x M ε hM hε
  refine ⟨δ, hδ, p, hp0, ?_⟩
  have hLip' : LipschitzWith (Real.toNNReal L) w := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa [Real.dist_eq, Real.coe_toNNReal, hL] using hLip u v
  have hDerBound (y : ℝ) : |deriv w y| ≤ L := by
    simpa only [Real.norm_eq_abs, Real.coe_toNNReal, hL] using
      (norm_deriv_le_of_lipschitz (x₀ := y) hLip')
  have hfCont : Continuous (fun r : ℝ =>
      Polynomial.eval (Real.exp (-r)) p) := by
    fun_prop
  have hfBound (r : ℝ) (hr : 0 ≤ r) :
      |Polynomial.eval (Real.exp (-r)) p| ≤ L + ε := by
    apply hpBound
    constructor
    · exact (Real.exp_pos _).le
    · exact Real.exp_le_one_iff.mpr (by linarith)
  intro b R hb hR
  apply avram_wave5_04c_C1_integrated_finite_band_large_residual_bound
    w hwC1 (fun r => Polynomial.eval (Real.exp (-r)) p)
    hfCont b R M ε L hR hM hε.le hL hDerBound hfBound
  intro r hr
  have hh := hpApprox b r hb hr
  rw [abs_sub_comm] at hh
  exact hh.le
