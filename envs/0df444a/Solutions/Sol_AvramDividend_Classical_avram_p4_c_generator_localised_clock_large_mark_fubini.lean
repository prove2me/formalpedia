-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:36:33.581111+00:00
-- url     : https://prove2.me/submissions/4c0c9743-1b3c-4d29-9a8d-4d596538eabb

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Fubini for raw original negative jumps retained only on a
measurable stopped clock region, with local cap assumption on that region. -/
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
    (∫ p : T × ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => w (R s.1 + s.2) - w (R s.1))) p
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, ({s : T × ℝ | s.1 ∈ A}.indicator
      (fun s => w (R s.1 + s.2) - w (R s.1))) (t,z)
      ∂(X.ν.restrict (Iio (-ε))) ∂μ := by
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (-ε))) :=
    (isFiniteMeasure_restrict).2 (ne_of_lt htail)
  exact integral_prod
    ({p : T × ℝ | p.1 ∈ A}.indicator
      (fun p => w (R p.1 + p.2) - w (R p.1)))
    (avram_p4_c_generator_localised_raw_large_mark_L1
      X μ R hR A hA w v ε hv hε hw_cont hw_neg hcap)
