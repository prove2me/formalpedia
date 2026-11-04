-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_weighted_raw_large_mark_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:15:50.910201+00:00
-- url     : https://prove2.me/submissions/1e5b4069-58f6-4a56-90ed-6aa712946c4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every measurable bounded clock weight preserves the original ν-large
raw-jump L¹ bound; this includes stopped discount weights once bounded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    Integrable
      (fun p : T × ℝ => a p.1 * (w (R p.1 + p.2) - w (R p.1)))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by
  have hI :=
    avram_p4_c_generator_finite_clock_raw_large_mark_L1
      X μ R hR w v ε hv hε hw_cont hw_neg hcap
  have hweight_meas : Measurable (fun p : T × ℝ => a p.1) :=
    ha.comp measurable_fst
  apply Integrable.bdd_mul hI hweight_meas.aestronglyMeasurable
    (c := M)
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs] using hweight p.1
