-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_strict_preruin_each_clipped_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:36:22.098411+00:00
-- url     : https://prove2.me/submissions/2da6ec8c-a3af-4a95-9c9d-ccbd547dd950

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : ℕ → Ω → ℝ≥0) (k j i : ℕ) (ω : Ω)
    (hPre : σ k ω = 0 ∨
      (σ k ω : ℝ≥0∞) < ruinTime X x D ω) :
    let v : ℝ≥0 :=
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ k ω)
    v = 0 ∨ (v : ℝ≥0∞) < ruinTime X x D ω := by
  dsimp
  rcases hPre with hz | hlt
  · left
    simp [hz]
  · right
    have hle : min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ k ω) ≤
        σ k ω := min_le_right _ _
    exact lt_of_le_of_lt (by exact_mod_cast hle) hlt
