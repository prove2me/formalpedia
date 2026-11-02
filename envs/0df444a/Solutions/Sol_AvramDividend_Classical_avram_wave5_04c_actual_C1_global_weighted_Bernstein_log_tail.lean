-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_global_weighted_Bernstein_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:29:08.139896+00:00
-- url     : https://prove2.me/submissions/c4cc28d4-aa95-409f-993e-5d34008c9cd2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile_quantitative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_log_quotient_Lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_envelope_log_growth
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_poly_error_from_cutoff_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! One polynomial simultaneously approximates the genuine C1 payoff on
every negative jump size: BV endpoint weight plus a distant-jump tail. -/
theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
          ε * (1 - (t : ℝ)) +
            (if (t : ℝ) < b then 2 * L * |Real.log (t : ℝ)| else 0) := by
  let f : ℝ → ℝ :=
    Function.update
      (fun t : ℝ => (w (x + Real.log t) - w x) / (t - 1))
      1 (deriv w x)
  have hf : ContinuousOn f (Icc a 1) :=
    avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
      w hw x a ha (le_trans (le_of_lt hab) hb)
  obtain ⟨G, hzero, hmatch, hbound⟩ :=
    avram_wave5_04c_tapered_compact_profile_quantitative f a b hab hb hf
  obtain ⟨Q, hQ, hQapprox⟩ :=
    avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
      G ε hε
  have hfgrowth : ∀ t : ℝ, a ≤ t → t ≤ 1 →
      |(1 - t) * f t| ≤ L * |Real.log t| := by
    intro t hat ht1
    exact avram_wave5_04c_C1_log_quotient_Lipschitz_bound
      w L hLip x t (lt_of_lt_of_le ha hat) ht1
  have hGgrowth : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ L * |Real.log (t : ℝ)| :=
    avram_wave5_04c_tapered_envelope_log_growth
      f G a L hL hzero hbound hfgrowth
  let g : ℝ → ℝ := fun t => w x - w (x + Real.log t)
  have hggrowth : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |g (t : ℝ)| ≤ L * |Real.log (t : ℝ)| := by
    intro t ht
    have h := hLip x (x + Real.log (t : ℝ))
    have hr : x - (x + Real.log (t : ℝ)) =
        -(Real.log (t : ℝ)) := by ring
    simpa [g, hr] using h
  have hGmatch : ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
      (1 - (t : ℝ)) * G t = g (t : ℝ) := by
    intro t ht
    by_cases h1 : (t : ℝ) = 1
    · simp [g, h1]
    · rw [hmatch t ht]
      have hfr : f (t : ℝ) =
          (w (x + Real.log (t : ℝ)) - w x) / ((t : ℝ) - 1) := by
        simp [f, h1]
      rw [hfr]
      have hne : (t : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
      dsimp [g]
      field_simp
      ring
  refine ⟨Q, hQ, ?_⟩
  exact avram_wave5_04c_global_poly_error_from_cutoff_bounds
    g G Q b ε L hQapprox hGmatch hGgrowth hggrowth
