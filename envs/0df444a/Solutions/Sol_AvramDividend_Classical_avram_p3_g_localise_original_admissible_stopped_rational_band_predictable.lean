-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_rational_band_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:32:31.772777+00:00
-- url     : https://prove2.me/submissions/c597944d-beea-43fa-ade6-05a7ffccf24f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_open_prestate_band_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every genuinely interior original stopped rational-band mask is
right-continuous predictable, including the stopping instant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a)
    (hBand : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Z p ∈ Ioo a b} := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  obtain ⟨_hBound, _hStop, hInterior, _hZero, _hCap⟩ :=
    avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
      X x C D hD T
  have hOpenBand :=
    avram_p3_g_localise_original_admissible_open_prestate_band_predictable
      X x C D hD a b
  have hEq :
      ({p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Z p ∈ Ioo a b} :
        Set (ℝ≥0 × Ω)) =
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C} ∩
      {p : ℝ≥0 × Ω | Z p ∈ Ioo a b} := by
    ext p
    constructor
    · rintro ⟨hStopped, hIoo⟩
      have hLower : a / 2 ≤ Z p := by linarith [hIoo.1]
      exact ⟨⟨hStopped, hBand ⟨hLower, le_of_lt hIoo.2⟩⟩, hIoo⟩
    · rintro ⟨⟨hStopped, _⟩, hIoo⟩
      exact ⟨hStopped, hIoo⟩
  change MeasurableSet[𝓕.rightCont.predictable]
    ({p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Z p ∈ Ioo a b})
  rw [hEq]
  exact hInterior.inter hOpenBand
