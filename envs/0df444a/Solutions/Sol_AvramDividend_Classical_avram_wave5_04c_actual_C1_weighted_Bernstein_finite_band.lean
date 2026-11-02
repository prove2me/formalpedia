-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_C1_weighted_Bernstein_finite_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:36:43.966672+00:00
-- url     : https://prove2.me/submissions/4997a8ee-d259-43f2-83fb-5c88e19d7400

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_tapered_compact_profile
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! Simultaneously approximate the C1 payoff loss on a finite negative
jump-size band by an endpoint-zero polynomial with exact BV weight. -/
theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (x a b ε : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
        |Polynomial.eval (t : ℝ) Q -
          (w x - w (x + Real.log (t : ℝ)))| ≤
            ε * (1 - (t : ℝ)) := by
  let f : ℝ → ℝ :=
    Function.update
      (fun t : ℝ => (w (x + Real.log t) - w x) / (t - 1))
      1 (deriv w x)
  have hf : ContinuousOn f (Icc a 1) :=
    avram_wave5_04c_actual_C1_logarithmic_quotient_continuous
      w hw x a ha (le_trans (le_of_lt hab) hb)
  obtain ⟨G, hzero, hmatch⟩ :=
    avram_wave5_04c_tapered_compact_profile f a b hab hb hf
  obtain ⟨Q, hQ, hQapprox⟩ :=
    avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
      G ε hε
  refine ⟨Q, hQ, ?_⟩
  intro t ht
  have hcorrect : (1 - (t : ℝ)) * G t =
      w x - w (x + Real.log (t : ℝ)) := by
    by_cases h1 : (t : ℝ) = 1
    · simp [h1]
    · rw [hmatch t ht]
      have hfr : f (t : ℝ) =
          (w (x + Real.log (t : ℝ)) - w x) / ((t : ℝ) - 1) := by
        simp [f, h1]
      rw [hfr]
      have hne : (t : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
      field_simp
      ring
  rw [← hcorrect]
  exact hQapprox t
