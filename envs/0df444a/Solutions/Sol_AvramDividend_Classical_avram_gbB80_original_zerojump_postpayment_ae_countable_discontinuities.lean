-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB80_original_zerojump_postpayment_ae_countable_discontinuities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:30:20.848148+00:00
-- url     : https://prove2.me/submissions/d86fbde2-0df2-400a-8265-ae9d04827a7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_gbB79_original_postpayment_reserve_discontinuities_countable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) :
    ∀ᵐ ω ∂P,
      Set.Countable {t : ℝ≥0 |
        ¬ ContinuousAt (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t} := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
    with ω hcontinuous
  exact avram_gbB79_original_postpayment_reserve_discontinuities_countable
    X D hD x ω hcontinuous
