-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_finite_band_polynomial_test_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:23:51.52513+00:00
-- url     : https://prove2.me/submissions/ffcc3a3c-df50-4b7d-98ec-1b8af6464168

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_two_finite_measures_ae_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Polynomial ℝ,
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - p.eval x| ≤ δ) ∧
      (Integrable (fun x : ℝ => p.eval x) μ →
       Integrable (fun x : ℝ => p.eval x) ν →
       |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
         |(∫ x, p.eval x ∂μ) - (∫ x, p.eval x ∂ν)| +
         δ * (μ.real Set.univ + ν.real Set.univ)) := by
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (0 : ℝ) 1 f hf δ hδ
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    rw [abs_sub_comm]
    exact le_of_lt (hp x hx)
  · intro hpμ hpν
    apply AvramDividend.Classical.avram_p2_b_rate_two_finite_measures_ae_comparison
      μ ν f (fun x => p.eval x) hfμ hpμ hfν hpν δ
    · filter_upwards [hμ] with x hx
      rw [abs_sub_comm]
      exact le_of_lt (hp x hx)
    · filter_upwards [hν] with x hx
      rw [abs_sub_comm]
      exact le_of_lt (hp x hx)