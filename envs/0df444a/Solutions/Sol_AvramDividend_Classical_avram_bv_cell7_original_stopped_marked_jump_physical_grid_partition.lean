-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:47:32.820213+00:00
-- url     : https://prove2.me/submissions/0dede9d3-982d-47c3-b5dd-0ae58f6fe6f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- True original Lévy marked-jump integrals partition exactly over the
    stopped physical dividend grid, including its single final contact cell. -/
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
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
      (fun v : ℝ≥0 => (v, Δ v))
  have hClock : u 0 = 0 ∧ u (m + 1) = min T τ ∧ Monotone u := by
    simpa only [u, τ] using
      (AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
        X x D T m ω)
  have hCell (a b c : ℝ≥0) (hab : a ≤ b) (hbc : b ≤ c) :
      (∫⁻ p, F p ∂N (Ioc a c)) =
        (∫⁻ p, F p ∂N (Ioc a b)) +
        (∫⁻ p, F p ∂N (Ioc b c)) := by
    simpa only [N, Δ] using
      (AvramDividend.Classical.avram_bv_cell7_original_marked_jump_weighted_halfopen_cell_add
        X ω a b c hab hbc F hF)
  have hPart : ∀ n : ℕ,
      (∫⁻ p, F p ∂N (Ioc (u 0) (u n))) =
        ∑ i ∈ Finset.range n,
          (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by
    intro n
    induction n with
    | zero => simp [N]
    | succ n ih =>
      calc
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (n + 1)))) =
            (∫⁻ p, F p ∂N (Ioc (u 0) (u n))) +
            (∫⁻ p, F p ∂N (Ioc (u n) (u (n + 1)))) :=
              hCell (u 0) (u n) (u (n + 1))
                (hClock.2.2 (Nat.zero_le n))
                (hClock.2.2 (Nat.le_succ n))
        _ = ∑ i ∈ Finset.range (n + 1),
              (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by
                rw [ih, Finset.sum_range_succ]
  exact ⟨hClock.1, hClock.2.1, hPart (m + 1)⟩
