-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_localised_weighted_raw_large_mark_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:21:46.972996+00:00
-- url     : https://prove2.me/submissions/789c4992-497e-45a0-9288-a2b49e4e5d89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original ν-large raw-jump payoff remains product L¹ after a
bounded discount and stopping-region mask; the cap holds only on A. -/
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
      ({p : T × ℝ | p.1 ∈ A}.indicator
        (fun p => a p.1 * (w (R p.1 + p.2) - w (R p.1))))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by
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
  have hI :=
    avram_p4_c_generator_finite_clock_raw_large_mark_L1
      X μ Rc hRcmeas w v ε hv hε hw_cont hw_neg hRccap
  have hweight_meas : Measurable (fun p : T × ℝ => a p.1) :=
    ha.comp measurable_fst
  have hweighted : Integrable
      (fun p : T × ℝ => a p.1 * (w (Rc p.1 + p.2) - w (Rc p.1)))
      (μ.prod (X.ν.restrict (Iio (-ε)))) := by
    apply Integrable.bdd_mul hI hweight_meas.aestronglyMeasurable (c := M)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs] using hweight p.1
  have hAprod : MeasurableSet {p : T × ℝ | p.1 ∈ A} :=
    hA.preimage measurable_fst
  have hEq :
      ({p : T × ℝ | p.1 ∈ A}.indicator
        (fun p => a p.1 * (w (Rc p.1 + p.2) - w (Rc p.1)))) =
      ({p : T × ℝ | p.1 ∈ A}.indicator
        (fun p => a p.1 * (w (R p.1 + p.2) - w (R p.1)))) := by
    funext p
    by_cases hp : p.1 ∈ A
    · simp [Set.indicator, hp, Rc]
    · simp [Set.indicator, hp, Rc]
  simpa only [hEq] using hweighted.indicator hAprod
