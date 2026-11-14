-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB37_original_shifted_candidate_ae_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:52:04.821699+00:00
-- url     : https://prove2.me/submissions/9eb8505e-a7ca-4a57-91d8-e81b6255ef9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Current-checker revalidated original Levy measure shifted-cap almost everywhere continuity; full physical negative jump support. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ)
    (hAway : ∀ r : ℝ, r ≠ 0 → ContinuousAt w r)
    (c : ℝ) :
    ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ContinuousAt w (c + z) := by
  have hz : X.ν ({-c} : Set ℝ) = 0 :=
    avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
      X hStanding hBV (-c)
  have hNull : (X.ν.restrict (Iio (0 : ℝ))) ({-c} : Set ℝ) = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton (-c))]
    exact measure_mono_null Set.inter_subset_left hz
  have hAe : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≠ -c := by
    apply (ae_iff).2
    simpa using hNull
  filter_upwards [hAe] with z hz'
  apply hAway
  intro heq
  apply hz'
  linarith
