-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_large_mark_factorised
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:31:39.115901+00:00
-- url     : https://prove2.me/submissions/f55290b6-3468-4ee1-9f24-5717e730b029

import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_large_mark_fubini
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- At a stopped interior reserve, the discounted original Levy large-jump
product integral is the time integral of the masked physical drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    (∫ p : T × ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => a s.1 * (w (R s.1 + s.2) - w (R s.1)))) p
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, (A.indicator (fun t => a t *
      (∫ z : ℝ, w (R t + z) - w (R t)
      ∂(X.ν.restrict (Iio (-ε)))))) t ∂μ := by
  have hF :=
    avram_p4_c_generator_localised_weighted_large_mark_fubini
      X μ R a hR ha A hA w v ε hv hε hw_cont hw_neg hcap M hweight
  rw [hF]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ A
  · simp [Set.indicator, ht, integral_const_mul]
  · simp [Set.indicator, ht]
