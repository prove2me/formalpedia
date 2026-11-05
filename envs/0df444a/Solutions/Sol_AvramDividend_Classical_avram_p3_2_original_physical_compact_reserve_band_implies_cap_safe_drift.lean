-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:03:34.109303+00:00
-- url     : https://prove2.me/submissions/58aff4ea-619b-446f-886c-f20376cd8ead

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original X/D strict compact reserve ceiling yields cap-safe physical drift cells without separately selecting a reserve margin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (C : ℝ≥0∞) (b : ℝ)
    (hb : C = ⊤ ∨ b < C.toReal)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1))
    (hCeil : ∀ m i, i < n m →
      x + X.X (u m i) ω - rightLimit D (u m i) ω ≤ b)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) :
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨
      x + X.X (u m i) ω - rightLimit D (u m i) ω +
        (((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift) ≤ C.toReal := by
  by_cases hTop : C = ⊤
  · exact Filter.Eventually.of_forall (fun m i hi => Or.inl hTop)
  · have hb' : b < C.toReal := hb.resolve_left hTop
    let ρ : ℝ := C.toReal - b
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hMargin : ∀ m i, i < n m →
        C = ⊤ ∨
          x + X.X (u m i) ω - rightLimit D (u m i) ω ≤
            C.toReal - ρ := by
      intro m i hi
      right
      dsimp [ρ]
      linarith [hCeil m i hi]
    have hResult :=
      avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid
        X x D ω C ρ hρ u n hGrid hMargin hSmall
    simpa only using hResult
