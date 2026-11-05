-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:51:43.031777+00:00
-- url     : https://prove2.me/submissions/fe69568f-19f4-4817-bde7-04691311e9dd

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_grid_total_variation_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine physical BV drift Taylor error tends to zero along strict-interior refining clocks. -/
theorem solution
    (b : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a d : ℝ)
    (hBand : Set.Icc a d ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (z : ℕ → ℕ → ℝ)
    (hStart : ∀ m, u m 0 = 0)
    (hEnd : ∀ m, u m (n m) = T)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1)) :
    let c : ℕ → ℕ → ℝ := fun m i =>
      ((u m (i + 1) : ℝ) - (u m i : ℝ)) * b
    (∀ m i, i < n m →
      Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a d) →
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
    ∀ η : ℝ, 0 < η →
      ∀ᶠ m in Filter.atTop,
        |∑ i ∈ Finset.range (n m),
          Real.exp (-(q * (u m i : ℝ))) *
            (w (z m i + c m i) - w (z m i) -
              deriv w (z m i) * c m i)| < η := by
  intro c hBandCells hClockSmall η hη
  let M : ℝ := (T : ℝ) * |b|
  let B : ℝ := |M| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg M]
  have hε : 0 < η / B := div_pos hη hB
  obtain ⟨δ, hδ, hCellBound⟩ :=
    avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
      w C hwC1 hOpen a d hBand q hq (η / B) hε
  have hShift :=
    avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
      b u n hGrid hClockSmall
  filter_upwards [hShift δ hδ] with m hSmall
  have hVar :
      (∑ i ∈ Finset.range (n m), |c m i|) = M := by
    have hRaw :=
      avram_p3_2_original_physical_drift_grid_total_variation_exact
        b (u m) (n m) (hGrid m)
    change (∑ i ∈ Finset.range (n m), |c m i|) =
      ((u m (n m) : ℝ) - (u m 0 : ℝ)) * |b| at hRaw
    simpa [hStart m, hEnd m, M] using hRaw
  have hEstimate :=
    hCellBound (u m) (n m) (z m) (c m)
      (hBandCells m) hSmall
  have hMB : M < B := by
    dsimp [B]
    linarith [le_abs_self M]
  calc
    |∑ i ∈ Finset.range (n m),
      Real.exp (-(q * (u m i : ℝ))) *
        (w (z m i + c m i) - w (z m i) -
          deriv w (z m i) * c m i)| ≤
        (η / B) * (∑ i ∈ Finset.range (n m), |c m i|) := hEstimate
    _ = (η / B) * M := by rw [hVar]
    _ < (η / B) * B := mul_lt_mul_of_pos_left hMB hε
    _ = η := by field_simp [ne_of_gt hB]
