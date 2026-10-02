-- Prove2me | solution 2 for ErlerGross.integral_cosh_div_cosh_eq_alternating_exp_tsum
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T18:48:25.291282+00:00
-- url     : https://prove2.me/submissions/566ff7a6-ddb1-47dd-8100-ebff6e999576

import Mathlib
import Definitions.Def_ErlerGross_defs

namespace ErlerGrossCex93fe

open Real Filter Topology MeasureTheory

/-- The alternating series at `a = 0`, `b = 1` is `∑ (-1)^n * 2/(2n+1)`, which is only
conditionally convergent, hence not `Summable` in `ℂ`. -/
theorem not_summable_93fe :
    ¬ Summable (fun n : ℕ => (-1 : ℂ)^n *
        (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) +
         1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))) := by
  intro h
  have hn := h.norm
  have hnorm : ∀ n : ℕ, ‖(-1 : ℂ)^n *
        (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) +
         1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0))‖ = 2 / (2 * (n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    have e : (1 / (((2 * n + 1 : ℕ) : ℂ) * 1 - 0) +
         1 / (((2 * n + 1 : ℕ) : ℂ) * 1 + 0)) = ((2 / (2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast
      simp only [mul_one, sub_zero, add_zero]
      ring
    rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [hnorm] at hn
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    linarith
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    rw [← summable_nat_add_iff 1]
    simpa [Nat.cast_add, Nat.cast_one] using h1
  exact Real.not_summable_one_div_natCast h2

theorem integrable_inv_cosh_93fe :
    IntegrableOn (fun x : ℝ => 1 / Real.cosh x) (Set.Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul 2) ?_ ?_
  · exact (continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')).aestronglyMeasurable
  · refine ae_of_all _ (fun x => ?_)
    have hc : 0 < Real.cosh x := Real.cosh_pos x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ hc, Real.cosh_eq]
    have h1 : Real.exp (-1 * x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    have h2 : 0 < Real.exp (-1 * x) * Real.exp (-x) := by positivity
    nlinarith

theorem fun_eq_93fe :
    (fun x : ℝ => Complex.cosh ((0 : ℂ) * x) / Complex.cosh ((1 : ℂ) * x)) =
      fun x : ℝ => ((1 / Real.cosh x : ℝ) : ℂ) := by
  funext x
  push_cast
  simp

theorem integral_pos_93fe :
    0 < ∫ x in Set.Ioi (0 : ℝ), 1 / Real.cosh x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => by
      have := Real.cosh_pos x
      simp only [Pi.zero_apply]; positivity) integrable_inv_cosh_93fe]
  have hs : Function.support (fun x : ℝ => 1 / Real.cosh x) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    have := Real.cosh_pos x
    positivity
  rw [hs, Measure.restrict_apply_univ, Real.volume_Ioi]
  simp

end ErlerGrossCex93fe

open Real Filter Topology MeasureTheory in
theorem solution : ¬ (∀ (a b : ℂ)
    (hab : |a.re| < b.re)
    (hI : IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x))
      (Set.Ioi 0)),
    ∫ x in Set.Ioi (0 : ℝ), Complex.cosh (a * x) / Complex.cosh (b * x) =
      ∑' n : ℕ, (-1 : ℂ)^n *
        (1 / (((2 * n + 1 : ℕ) : ℂ) * b - a) +
         1 / (((2 * n + 1 : ℕ) : ℂ) * b + a))) := by
  intro h
  have hab : |(0 : ℂ).re| < (1 : ℂ).re := by simp
  have hI : IntegrableOn (fun x : ℝ => Complex.cosh ((0 : ℂ) * x) / Complex.cosh ((1 : ℂ) * x))
      (Set.Ioi 0) := by
    rw [ErlerGrossCex93fe.fun_eq_93fe]
    exact ErlerGrossCex93fe.integrable_inv_cosh_93fe.ofReal
  have key := h 0 1 hab hI
  rw [tsum_eq_zero_of_not_summable ErlerGrossCex93fe.not_summable_93fe,
    ErlerGrossCex93fe.fun_eq_93fe, integral_complex_ofReal] at key
  have hp := ErlerGrossCex93fe.integral_pos_93fe
  have : (∫ x in Set.Ioi (0 : ℝ), 1 / Real.cosh x) = 0 := by exact_mod_cast key
  linarith
