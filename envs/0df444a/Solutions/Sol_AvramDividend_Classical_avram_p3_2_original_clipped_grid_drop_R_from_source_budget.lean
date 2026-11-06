-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_clipped_grid_drop_R_from_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:27:27.729451+00:00
-- url     : https://prove2.me/submissions/dd930813-c723-4be7-a38d-2dc8b851ee21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- On original stopped clipped BV physical grids, any genuine pathwise cash-source
budget with its explicit intrinsic R correction transfers to the same budget
without that correction, even with sample-dependent grid length. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω, Monotone (u ω))
    (n : Ω → ℕ) (F M B : Ω → ℝ)
    (hRaw :
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let G : Ω → ℝ := fun ω =>
        let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) -
            (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
              ENNReal.ofReal
                (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
              else 0).toReal
        ∑ i : Fin (n ω),
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))
      ∀ᵐ ω ∂P, F ω ≤ w x + (M ω + B ω) + G ω) :
    ∀ᵐ ω ∂P, F ω ≤ w x + (M ω + B ω) := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  let G : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    ∑ i : Fin (n ω),
      Real.exp (-(q * (v i : ℝ))) *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  have h := avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad q
  dsimp only at h
  change ∀ᵐ ω ∂P, F ω ≤ w x + (M ω + B ω) + G ω at hRaw
  have hG : ∀ᵐ ω ∂P, G ω ≤ 0 := by
    filter_upwards [h] with ω hω
    have hv : Monotone (fun i : ℕ => min (u ω i) (τ ω)) := by
      intro i j hij
      exact le_min ((min_le_left _ _).trans (hu ω hij)) (min_le_right _ _)
    exact hω.2 τ (fun i : ℕ => min (u ω i) (τ ω)) hv
      (n ω) (min_le_right _ _)
  filter_upwards [hRaw, hG] with ω hr hg
  linarith
