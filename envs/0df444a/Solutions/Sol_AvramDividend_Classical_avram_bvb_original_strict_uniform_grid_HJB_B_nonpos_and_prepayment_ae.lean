-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:56:21.151758+00:00
-- url     : https://prove2.me/submissions/f4edd1ff-5b24-42ff-989b-e87b2775817f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
import Theorems.Thm_AvramDividend_Classical_avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1))
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun n i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let clock : ℕ → ℕ → Ω → Prop := fun n i ω =>
      (u n i : ℝ≥0∞) < ruinTime X x D ω
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) v - X.X v ω
         else 0)
    let coeff : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n i ω)
      else 0
    let G : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range (n + 1),
        if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    let B : ℕ → Ω → ℝ := fun n ω => G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))
    (∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) ∧
    (∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)  := by
  dsimp
  constructor
  · simpa only using
      (avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
        X hX hBV q w C hGen x D u hu)
  · exact avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
      X x D hD T hT u huniform
