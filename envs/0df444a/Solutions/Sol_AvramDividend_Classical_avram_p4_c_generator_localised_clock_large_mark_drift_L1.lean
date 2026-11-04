-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:36.789219+00:00
-- url     : https://prove2.me/submissions/dbdd34ac-b6d3-4c9c-adfa-b49ec010ce0e

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source ν-large jump drift is time-L¹ on a true measurable stopped
region, requiring the reserve cap only on the retained clock states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v) :
    Integrable
      (A.indicator (fun t : T =>
        ∫ z : ℝ, w (R t + z) - w (R t)
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
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (-ε))) :=
    (isFiniteMeasure_restrict).2 (ne_of_lt htail)
  have hI : Integrable
      (fun t : T => ∫ z : ℝ, w (Rc t + z) - w (Rc t)
        ∂(X.ν.restrict (Iio (-ε)))) μ :=
    (avram_p4_c_generator_finite_clock_raw_large_mark_L1
      X μ Rc hRcmeas w v ε hv hε hw_cont hw_neg hRccap).integral_prod_left
  have hEq :
      (A.indicator (fun t : T =>
        ∫ z : ℝ, w (Rc t + z) - w (Rc t)
          ∂(X.ν.restrict (Iio (-ε))))) =
      (A.indicator (fun t : T =>
        ∫ z : ℝ, w (R t + z) - w (R t)
          ∂(X.ν.restrict (Iio (-ε))))) := by
    funext t
    by_cases ht : t ∈ A
    · simp [Set.indicator, ht, Rc]
    · simp [Set.indicator, ht, Rc]
  simpa only [hEq] using hI.indicator hA
