-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ae_safe_interval_implies_positive_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:55:48.247518+00:00
-- url     : https://prove2.me/submissions/03a33409-3fa1-497e-8e65-55378092caa8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Almost-sure source pathwise safety implies positive original ruin time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hSafeAE : ∀ᵐ ω ∂P, ∃ ε : ℝ≥0,
      0 < ε ∧ ∀ t : ℝ≥0, t < ε → 0 ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω := by
  filter_upwards [hSafeAE] with ω hω
  obtain ⟨ε, hε, hSafe⟩ := hω
  have hLower : (ε : ℝ≥0∞) ≤ ruinTime X x D ω :=
    avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
      X x D ω ε hSafe
  have hεpos : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast hε
  exact hεpos.trans_le hLower
