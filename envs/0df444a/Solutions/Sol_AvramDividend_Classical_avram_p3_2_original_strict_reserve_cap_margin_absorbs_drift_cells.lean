-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:43:14.733652+00:00
-- url     : https://prove2.me/submissions/8e2d8d91-a13f-4bfa-8697-2d85a11eba9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Strict original reserve cap margin absorbs eventual physical BV drift upshifts. -/
theorem solution
    (C : ℝ≥0∞) (ρ : ℝ) (hρ : 0 < ρ)
    (z c : ℕ → ℕ → ℝ) (n : ℕ → ℕ)
    (hInterior : ∀ m i, i < n m →
      C = ⊤ ∨ z m i ≤ C.toReal - ρ)
    (hDriftSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        |c m i| < ε) :
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨ z m i + c m i ≤ C.toReal := by
  filter_upwards [hDriftSmall ρ hρ] with m hCell
  intro i hi
  rcases hInterior m i hi with hTop | hBelow
  · exact Or.inl hTop
  · right
    have hShiftUpper : c m i ≤ |c m i| := le_abs_self _
    have hSmall := hCell i hi
    linarith
