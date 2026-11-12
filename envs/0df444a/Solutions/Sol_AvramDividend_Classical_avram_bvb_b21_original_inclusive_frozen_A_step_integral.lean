-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_inclusive_frozen_A_step_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:11:56.555348+00:00
-- url     : https://prove2.me/submissions/854fb74f-30ce-4939-b733-fc39cfa71595

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_frozen_grid_sum_as_step_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact inclusive-cap original marked compensator is a step integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let c : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ Z i ∧ ENNReal.ofReal (Z i) ≤ C then
        ∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
          (w (Z i + z) - w (Z i)) ∂X.ν
      else 0
    (∑ i ∈ Finset.range (n + 1),
      c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
      ∫ t : ℝ, ∑ i ∈ Finset.range (n + 1),
        (Ico (u n i : ℝ) (u n (i + 1) : ℝ)).indicator
          (fun _ => c i) t := by
  dsimp only
  let c : ℕ → ℝ := fun i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 ≤ Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
        ENNReal.ofReal (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) ≤ C then
      ∫ z in Iio (0 : ℝ), Real.exp (-(q * (u n i : ℝ))) *
        (w (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) + z) -
         w (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i))) ∂X.ν
    else 0
  have hu : ∀ i < n + 1, (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
    intro i hi
    exact_mod_cast hmono n i hi
  change (∑ i ∈ Finset.range (n + 1),
      c i * ((u n (i + 1) : ℝ) - (u n i : ℝ))) =
    ∫ t : ℝ, ∑ i ∈ Finset.range (n + 1),
      (Ico (u n i : ℝ) (u n (i + 1) : ℝ)).indicator
        (fun _ => c i) t
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        ((u n (i + 1) : ℝ) - (u n i : ℝ)) * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := (avram_bvb_b21_original_frozen_grid_sum_as_step_integral
      (n + 1) (fun i => (u n i : ℝ)) c hu).symm
