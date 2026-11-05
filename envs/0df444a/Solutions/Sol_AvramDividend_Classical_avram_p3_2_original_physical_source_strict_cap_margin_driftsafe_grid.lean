-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:53:58.533407+00:00
-- url     : https://prove2.me/submissions/1a666ec8-9a54-4a29-9756-99f1bc7bf45a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A strict cap reserve strip makes the actual X/D physical BV drift grid cap-safe eventually. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (C : ℝ≥0∞) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1)) :
    let z : ℕ → ℕ → ℝ := fun m i =>
      x + X.X (u m i) ω - rightLimit D (u m i) ω
    let c : ℕ → ℕ → ℝ := fun m i =>
      ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
    (∀ m i, i < n m → C = ⊤ ∨ z m i ≤ C.toReal - ρ) →
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨ z m i + c m i ≤ C.toReal := by
  intro z c hInterior hClockSmall
  have hShift :=
    avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
      X.drift u n hGrid hClockSmall
  exact avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells
    C ρ hρ z c n hInterior hShift
