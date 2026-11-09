-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_original_canonical_B_nonpositive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:11:29.381855+00:00
-- url     : https://prove2.me/submissions/b0c80d58-be4a-48a5-aa77-072f3ed1e7b1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_grid_B_nonpositive_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) *
                (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ))
            else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
           let R : ℝ≥0 → ℝ := fun t =>
             ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))) :
    ∀ᵐ ω ∂P, ∀ n, B n ω ≤ 0 := by
  let Z : ℕ → Ω → ℕ → ℝ := fun n ω i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let good : ℕ → Ω → ℕ → Prop := fun n ω i =>
    (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
      0 < Z n ω i ∧ ENNReal.ofReal (Z n ω i) < C
  let A : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    if good n ω i then
      Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n ω i)
    else 0
  refine avram_bv_tail12_original_grid_B_nonpositive_ae
    X hX hBV q w C hw_gen u hmono Z good ?_ A B ?_
  · intro n ω i hi
    exact ⟨hi.2.1, hi.2.2⟩
  · intro n ω
    simpa only [Z, good, A] using hB n ω
