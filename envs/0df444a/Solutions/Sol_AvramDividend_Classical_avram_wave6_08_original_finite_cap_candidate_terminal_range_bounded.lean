-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_finite_cap_candidate_terminal_range_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:17:31.007504+00:00
-- url     : https://prove2.me/submissions/2e60c540-b9f1-428b-a1e0-859495792c50

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Bornology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual finite-cap pre-ruin reserve has bounded verification-value range.
This includes t = 0 and initial capital equal to the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) :
    Bornology.IsBounded { z : ℝ | ∃ ω : Ω, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω ∧
      z = w (riskProcess X x D t ω) } := by
  have hcont : ContinuousOn w (Icc (0 : ℝ) c) :=
    hw_cont.mono (by
      intro y hy
      exact hy.1)
  have hbdd : Bornology.IsBounded (w '' Icc (0 : ℝ) c) :=
    (isCompact_Icc.image_of_continuousOn hcont).isBounded
  apply hbdd.subset
  rintro z ⟨ω, t, ht, hz⟩
  subst z
  have hx0 : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg
      X x (ENNReal.ofReal c) hxc D hD
  have hzero : 0 ≤ riskProcess X x D t ω :=
    (capped_riskProcess_range_before_ruin_including_zero
      X x hx0 (ENNReal.ofReal c) hxc D hD ω t ht).1
  have hcap : riskProcess X x D t ω ≤ c :=
    avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
      X x c hc hxc D hD ω t ht
  exact ⟨riskProcess X x D t ω, ⟨hzero, hcap⟩, rfl⟩
