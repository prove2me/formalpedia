-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:26:20.8762+00:00
-- url     : https://prove2.me/submissions/1d7080d7-c2ce-43d5-9cb5-aa759a5ef578

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The accepted unrestricted ENNReal reserve cap yields the requested
finite real reserve bound, including the initial endpoint and x=c. -/
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
  have hCap :
      ENNReal.ofReal (riskProcess X x D s ω) ≤
        ENNReal.ofReal c :=
    admissibleLe_riskProcess_le_cap_all_times
      X x (ENNReal.ofReal c) D hD hxc ω s
  exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hc)).mp hCap
