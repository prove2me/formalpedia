-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_finite_stopped_rational_bands_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:42:30.09153+00:00
-- url     : https://prove2.me/submissions/0418d7b5-d1db-419d-86da-a94a647e7877

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_rational_band_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite collection of genuine original stopped interior rational
bands is predictable, for deterministic finite-strip approximation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (S : Finset (ℚ × ℚ))
    (hBands : ∀ ab ∈ S,
      0 < (ab.1 : ℝ) ∧
      Icc ((ab.1 : ℝ) / 2) (ab.2 : ℝ) ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      (⋃ ab ∈ S,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)}) := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let Z : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  change MeasurableSet[𝓕.rightCont.predictable]
    (⋃ ab ∈ S,
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)})
  apply Finset.measurableSet_biUnion S
  intro ab hab
  obtain ⟨ha, hBand⟩ := hBands ab hab
  exact avram_p3_g_localise_original_admissible_stopped_rational_band_predictable
    X x C D hD T (ab.1 : ℝ) (ab.2 : ℝ) ha hBand
