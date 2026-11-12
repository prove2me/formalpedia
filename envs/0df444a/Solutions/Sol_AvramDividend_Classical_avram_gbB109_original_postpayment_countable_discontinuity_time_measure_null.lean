-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB109_original_postpayment_countable_discontinuity_time_measure_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:54:36.027544+00:00
-- url     : https://prove2.me/submissions/7f5abf74-145c-4429-ac7e-7899002ba574

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, μ
      {t : ℝ≥0 | ¬ ContinuousAt
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} = 0 := by
  have h :=
    avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
      X hν D hD x
  filter_upwards [h] with ω hω
  exact hω.measure_zero μ
