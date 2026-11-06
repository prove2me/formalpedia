-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_full_refining_Y_grid_small_of_first_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:21:52.154762+00:00
-- url     : https://prove2.me/submissions/dd6a58f8-57d9-47ac-9154-2923c152ccfb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_clock_refining_Y_grid_small
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original BV jump-removed Y mesh fineness reduces to the independently controlled zero-origin cell and the positive-clock tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (a b : ℝ≥0) (ha : 0 < a)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        (∀ m i, 0 < i → i < n m →
          u m i ∈ Set.Icc a b ∧ u m (i + 1) ∈ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop,
            ∀ i, 0 < i → i < n m →
              dist (u m (i + 1)) (u m i) < δ) →
        (∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            0 < n m → |Y (u m 1) - Y (u m 0)| < ε) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m →
              |Y (u m (i + 1)) - Y (u m i)| < ε := by
  filter_upwards
    [avram_p3_f2_original_positive_clock_refining_Y_grid_small X hBV]
      with ω hY
  intro a b ha u n Y hTailBand hTailClock hFirst ε hε
  let v : ℕ → ℕ → ℝ≥0 := fun m i => u m (i + 1)
  let k : ℕ → ℕ := fun m => n m - 1
  have hBandV :
      ∀ m i, i < k m →
        v m i ∈ Set.Icc a b ∧ v m (i + 1) ∈ Set.Icc a b := by
    intro m i hi
    have hij : i + 1 < n m := by
      dsimp [k] at hi
      omega
    simpa only [v, add_assoc] using
      hTailBand m (i + 1) (by omega) hij
  have hClockV :
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ m in Filter.atTop,
          ∀ i, i < k m →
            dist (v m (i + 1)) (v m i) < δ := by
    intro δ hδ
    filter_upwards [hTailClock δ hδ] with m hm
    intro i hi
    have hij : i + 1 < n m := by
      dsimp [k] at hi
      omega
    simpa only [v, add_assoc] using
      hm (i + 1) (by omega) hij
  have hTail := hY a b ha v k hBandV hClockV ε hε
  filter_upwards [hTail, hFirst ε hε] with m hT hF
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    exact hF hi
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hk : i - 1 < k m := by
      dsimp [k]
      omega
    have hiEq : i = (i - 1) + 1 := by omega
    rw [hiEq]
    simpa only [v] using hT (i - 1) hk
