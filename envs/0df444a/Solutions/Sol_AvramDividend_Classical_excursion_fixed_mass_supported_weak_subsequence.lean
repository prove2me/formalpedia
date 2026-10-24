-- Prove2me | solution 1 for AvramDividend.Classical.excursion_fixed_mass_supported_weak_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:42:33.939892+00:00
-- url     : https://prove2.me/submissions/1d4f5426-b137-418f-898d-cbabacded0da

import Mathlib.MeasureTheory.Measure.Prokhorov
import Theorems.Thm_AvramDividend_Classical_excursion_fixed_mass_normalized_prokhorov_subsequence
import Theorems.Thm_AvramDividend_Classical_excursion_finite_measure_normalize_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_probability_weak_limit_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_excursion_rescaled_probability_support_mass
import Theorems.Thm_AvramDividend_Classical_excursion_rescale_normalized_weak_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set

/-!
Uniform tightness, fixed positive mass and nonnegative support give
a subsequential finite-measure weak limit of the same mass and support.
-/
theorem solution
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (hsupport : ∀ n : ℕ, (ν n : Measure ℝ) (Iio (0 : ℝ)) = 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n : ℕ => ν (φ n)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ) (Iio (0 : ℝ)) = 0 ∧
      (μ : Measure ℝ) Set.univ = (c : ENNReal) := by
  obtain ⟨P, φ, hφ, hlim⟩ :=
    AvramDividend.Classical.excursion_fixed_mass_normalized_prokhorov_subsequence
      ν c hc hmass hnz htight
  have hPsup : (P : Measure ℝ) (Iio (0 : ℝ)) = 0 := by
    apply AvramDividend.Classical.excursion_probability_weak_limit_nonnegative_support
      (fun n => (ν (φ n)).normalize) P hlim
    intro n
    apply (ProbabilityMeasure.null_iff_toMeasure_null _ _).mp
    apply AvramDividend.Classical.excursion_finite_measure_normalize_nonnegative_support
      (ν (φ n)) (hnz (φ n))
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact hsupport (φ n)
  let μ : FiniteMeasure ℝ := c • P.toFiniteMeasure
  obtain ⟨hμsup, hμmass⟩ :=
    AvramDividend.Classical.excursion_rescaled_probability_support_mass P c hPsup
  refine ⟨μ, φ, hφ, ?_, ?_, ?_⟩
  · exact AvramDividend.Classical.excursion_rescale_normalized_weak_limit
      ν c hmass P φ hlim
  · exact hμsup
  · exact hμmass
