-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid14_original_pre_ruin_masked_cell_sum_cofinal_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:41:46.527073+00:00
-- url     : https://prove2.me/submissions/e203d4d0-b4cf-4d04-b7c2-652afb9b9a3b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (ω : Ω) (cell : ℕ → ℝ) :
    let Z : ℕ → ℝ := fun i =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∃ N : ℕ, ∀ k ≥ N,
      (∑ i ∈ Finset.range (n + 1),
        if ((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            (0 < Z i ∧ ENNReal.ofReal (Z i) < C)) ∧
            Z i ∈ Icc (a k) (b k) then cell i else 0) =
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            (0 < Z i ∧ ENNReal.ofReal (Z i) < C)
        then cell i else 0) := by
  classical
  dsimp only
  let Z : ℕ → ℝ := fun i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  obtain ⟨N, hN⟩ :=
    avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
      C a b hExh n Z
  refine ⟨N, ?_⟩
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  have hiff :
      (((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        (0 < Z i ∧ ENNReal.ofReal (Z i) < C)) ∧
        Z i ∈ Icc (a k) (b k)) ↔
      ((u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        (0 < Z i ∧ ENNReal.ofReal (Z i) < C)) := by
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, hN k hk i (Finset.mem_range.mp hi) h.2⟩
  exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)
