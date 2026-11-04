-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_weighted_clock_large_mark_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:45.673652+00:00
-- url     : https://prove2.me/submissions/c4614e83-8b45-4c44-a5a6-6a6be9ed3ae9

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_weighted_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Fubini for the original discounted negative large-jump raw payoff,
under bounded weights and capped reserves on a finite clock. -/
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
    (∫ p : T × ℝ, a p.1 * (w (R p.1 + p.2) - w (R p.1))
      ∂(μ.prod (X.ν.restrict (Iio (-ε))))) =
    ∫ t : T, ∫ z : ℝ, a t * (w (R t + z) - w (R t))
      ∂(X.ν.restrict (Iio (-ε))) ∂μ := by
  have htail : X.ν (Iio (-ε)) < ⊤ :=
    avram_p4_c_generator_epsilon_large_jump_intensity_finite X ε hε
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (-ε))) :=
    (isFiniteMeasure_restrict).2 (ne_of_lt htail)
  exact integral_prod
    (fun p : T × ℝ => a p.1 * (w (R p.1 + p.2) - w (R p.1)))
    (avram_p4_c_generator_weighted_raw_large_mark_L1
      X μ R a hR ha w v ε hv hε hw_cont hw_neg hcap M hweight)
