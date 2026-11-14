-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:47:21.895538+00:00
-- url     : https://prove2.me/submissions/a3d17478-4043-42de-b9a0-97518780577a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (ω : Ω) (S : ℝ≥0)
    (hzero : ∀ n, u n 0 = 0)
    (hBound : ∀ n i, i ≤ n + 1 → u n i ≤ S)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ))
      atTop (𝓝 (0 : ℝ)))
    (hPre : ∀ n i : ℕ,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
      riskProcess X x D t ω = 0) :
    let Z : ℕ → ℕ → ℝ := fun n i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let G : ℕ → ℕ → ℝ := fun n i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z n i ∧ ENNReal.ofReal (Z n i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n i) - q * w (Z n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), G n i)
      atTop (𝓝 (0 : ℝ))  := by
  let Z : ℕ → ℕ → ℝ := fun n i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let G : ℕ → ℕ → ℝ := fun n i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z n i ∧ ENNReal.ofReal (Z n i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z n i) - q * w (Z n i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  have hFirst :=
    avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
      X x D w C q ω u hzero hmesh
  have hFirstG : Tendsto (fun n => G n 0) atTop (𝓝 (0 : ℝ)) := by
    convert hFirst using 1
    ext n
    dsimp [G, Z]
    split_ifs <;> ring
  have hEvery (n : ℕ) :
      (∑ i ∈ Finset.range (n + 1), G n i) = G n 0 := by
    have h :=
      avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
        X x D w C q u n ω S (hBound n) (hPre n) hZero
    exact h
  have hFun :
      (fun n => ∑ i ∈ Finset.range (n + 1), G n i) =
        (fun n => G n 0) := by
    funext n
    exact hEvery n
  have hFinal : Tendsto (fun n =>
      ∑ i ∈ Finset.range (n + 1), G n i)
      atTop (𝓝 (0 : ℝ)) := by
    rw [hFun]
    exact hFirstG
  exact hFinal
