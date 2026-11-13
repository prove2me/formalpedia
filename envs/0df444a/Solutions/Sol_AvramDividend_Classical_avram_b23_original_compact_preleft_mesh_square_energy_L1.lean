-- Prove2me | solution 1 for AvramDividend.Classical.avram_b23_original_compact_preleft_mesh_square_energy_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:06:41.643215+00:00
-- url     : https://prove2.me/submissions/9620311a-b050-40e9-a6cb-c5c459afe174

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite original Lévy increments staying in one compact reserve band have event-local square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ (A : Set Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0),
      let z : Ω → ℕ → ℝ := fun ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s i)
      let g : Ω → ℕ → ℝ := fun ω i =>
        X.X (t i) ω - X.X (s i) ω - ((t i - s i) : ℝ) * X.c
      let Q : Ω → ℝ := fun ω => ∑ i ∈ S, (g ω i) ^ 2
      (∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S,
        z ω i ∈ Icc a b ∧ z ω i + g ω i ∈ Icc a b) →
      AEStronglyMeasurable Q (P.restrict A) →
      IntegrableOn Q A P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A S s t
  dsimp only
  intro hBand hMeas
  have hFinite : P A < ⊤ := measure_lt_top P A
  apply IntegrableOn.of_bound hFinite hMeas
    ((S.card : ℝ) * (b - a) ^ 2)
  filter_upwards [hBand] with ω hω
  have hNonneg : 0 ≤ ∑ i ∈ S,
      (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  calc
    (∑ i ∈ S, (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c) ^ 2) ≤
        ∑ i ∈ S, (b - a) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hz, hzg⟩ := hω i hi
      rcases Set.mem_Icc.mp hz with ⟨hza, hzb⟩
      rcases Set.mem_Icc.mp hzg with ⟨hga, hgb⟩
      have hMinus : 0 ≤ (b - a) -
          (X.X (t i) ω - X.X (s i) ω -
            ((t i - s i) : ℝ) * X.c) := by
        linarith
      have hPlus : 0 ≤ (b - a) +
          (X.X (t i) ω - X.X (s i) ω -
            ((t i - s i) : ℝ) * X.c) := by
        linarith
      nlinarith [mul_nonneg hMinus hPlus]
    _ = (S.card : ℝ) * (b - a) ^ 2 := by simp
