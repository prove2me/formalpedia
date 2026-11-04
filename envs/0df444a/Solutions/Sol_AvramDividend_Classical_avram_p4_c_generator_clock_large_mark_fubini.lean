-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_clock_large_mark_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:15:56.748197+00:00
-- url     : https://prove2.me/submissions/797b9eeb-d181-49c2-958a-ae887aeb98ea

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Fubini identifies the genuine original ν-large raw mark drift across
a finite clock; jump-count compensation remains an independent P2 task. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    (∫ p : T × ℝ, w (R p.1 + p.2) - w (R p.1)
        ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, w (R t + z) - w (R t)
        ∂(X.ν.restrict (Iio (-ε))) ∂μ := by
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (-ε))) :=
    (isFiniteMeasure_restrict).2 (ne_of_lt htail)
  exact integral_prod
    (fun p : T × ℝ => w (R p.1 + p.2) - w (R p.1))
    (avram_p4_c_generator_finite_clock_raw_large_mark_L1
      X μ R hR w v ε hv hε hw_cont hw_neg hcap)
