-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_monotone_eventual_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:57:44.771787+00:00
-- url     : https://prove2.me/submissions/8ece5b34-798b-4603-a88d-7217b2475cfc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- Physical generator cutoff approximants decrease and eventually equal their raw grid pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) (K L : ℝ) (hKL : K ≤ L) :
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    let H : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∑ i ∈ Finset.range (n + 1), max (-L) (H i)) ≤
      (∑ i ∈ Finset.range (n + 1), max (-K) (H i)) ∧
      ∃ N : ℕ, ∀ M ≥ N,
        (∑ i ∈ Finset.range (n + 1), max (-(M : ℝ)) (H i)) =
          ∑ i ∈ Finset.range (n + 1), H i := by
  let Z : ℕ → ℝ := fun j => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
  let H : ℕ → ℝ := fun i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change (∑ i ∈ Finset.range (n + 1), max (-L) (H i)) ≤
      (∑ i ∈ Finset.range (n + 1), max (-K) (H i)) ∧
      ∃ N : ℕ, ∀ M ≥ N,
        (∑ i ∈ Finset.range (n + 1), max (-(M : ℝ)) (H i)) =
          ∑ i ∈ Finset.range (n + 1), H i
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    refine max_le ?_ ?_
    · exact (neg_le_neg hKL).trans (le_max_left _ _)
    · exact le_max_right _ _
  · exact avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
      X q w C x D u n ω
