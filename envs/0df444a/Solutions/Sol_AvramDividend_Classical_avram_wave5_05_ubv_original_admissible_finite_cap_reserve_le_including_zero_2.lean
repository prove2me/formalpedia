-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:26:52.349247+00:00
-- url     : https://prove2.me/submissions/ad5eeb6a-e368-42e4-881d-81ffe0a7298f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ (ω : Ω) (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D s ω ≤ c := by
  intro ω s hs
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x (ENNReal.ofReal c) hxc D hD
  obtain ⟨_, hcap⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx (ENNReal.ofReal c) hxc D hD ω s hs
  exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hc)).mp hcap
