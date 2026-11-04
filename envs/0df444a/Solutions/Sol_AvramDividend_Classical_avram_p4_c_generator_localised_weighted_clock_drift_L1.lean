-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:41.243288+00:00
-- url     : https://prove2.me/submissions/3283f710-9ba4-4daf-8957-9ca72cc314ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_clock_large_mark_drift_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Discounted original ν-large-jump drift is time-L¹ on the stopped
region, and the actual reserve cap is needed only on that region. -/
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
    Integrable
      (A.indicator (fun t : T =>
        a t * ∫ z : ℝ, w (R t + z) - w (R t)
          ∂(X.ν.restrict (Iio (-ε))))) μ := by
  classical
  let Rc : T → ℝ := fun t => if t ∈ A then R t else 0
  have hRcmeas : Measurable Rc :=
    Measurable.ite hA hR measurable_const
  have hRccap : ∀ t : T, Rc t ∈ Icc 0 v := by
    intro t
    by_cases ht : t ∈ A
    · simpa only [Rc, if_pos ht] using hcap t ht
    · simpa only [Rc, if_neg ht] using
        (show (0 : ℝ) ∈ Icc 0 v from ⟨le_refl 0, hv⟩)
  have hI : Integrable
      (fun t : T => ∫ z : ℝ, w (Rc t + z) - w (Rc t)
        ∂(X.ν.restrict (Iio (-ε)))) μ :=
    avram_p4_c_generator_clock_large_mark_drift_L1
      X μ Rc hRcmeas w v ε hv hε hw_cont hw_neg hRccap
  have hweighted : Integrable
      (fun t : T => a t * (∫ z : ℝ, w (Rc t + z) - w (Rc t)
        ∂(X.ν.restrict (Iio (-ε))))) μ := by
    apply Integrable.bdd_mul hI ha.aestronglyMeasurable (c := M)
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using hweight t
  have hEq :
      (A.indicator (fun t : T =>
        a t * ∫ z : ℝ, w (Rc t + z) - w (Rc t)
          ∂(X.ν.restrict (Iio (-ε))))) =
      (A.indicator (fun t : T =>
        a t * ∫ z : ℝ, w (R t + z) - w (R t)
          ∂(X.ν.restrict (Iio (-ε))))) := by
    funext t
    by_cases ht : t ∈ A
    · simp [Set.indicator, ht, Rc]
    · simp [Set.indicator, ht, Rc]
  simpa only [hEq] using hweighted.indicator hA
