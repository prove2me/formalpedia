-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:47:46.074697+00:00
-- url     : https://prove2.me/submissions/c3c64162-b0d3-479f-941b-7ec179e09629

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original stopped intrinsic marked integral is exactly the sum
    of actual jump-time series over every physical cell, through contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        (∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            F (v, Δ v) else 0) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
      (fun v : ℝ≥0 => (v, Δ v))
  obtain ⟨h0, hT, hGrid⟩ :=
    (AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
      X x D T m ω F hF)
  refine ⟨h0, hT, ?_⟩
  calc
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
        ∑ i ∈ Finset.range (m + 1),
          (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := hGrid
    _ = ∑ i ∈ Finset.range (m + 1),
          (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              F (v, Δ v) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [N, Δ] using
        (AvramDividend.Classical.avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
          X ω (u i) (u (i + 1)) F hF)
