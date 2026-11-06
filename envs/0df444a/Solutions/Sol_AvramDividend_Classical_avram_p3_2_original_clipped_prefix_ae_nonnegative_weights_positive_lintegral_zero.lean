-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_nonnegative_weights_positive_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:59:35.566943+00:00
-- url     : https://prove2.me/submissions/32340348-aace-4d6b-aec0-c7bb4e97c8dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original clipped finite-prefix nonlinear BV correction has zero
positive outer mass with cell weights nonnegative only almost everywhere. -/
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
    (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (n : Ω → ℕ) (a : Ω → ℕ → ℝ)
    (hu : ∀ ω i, i < n ω → u ω i ≤ u ω (i + 1))
    (ha : ∀ᵐ ω ∂P, ∀ i, 0 ≤ a ω i) :
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
        a ω i *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by
  let a' : Ω → ℕ → ℝ := fun ω i => max 0 (a ω i)
  have ha' : ∀ ω i, 0 ≤ a' ω i := by
    intro ω i
    exact le_max_left _ _
  have h := avram_p3_2_original_clipped_finite_prefix_arbitrary_weights_positive_lintegral_zero
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    τ u n a' hu ha'
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
      a ω i *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  let G' : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    ∑ i : Fin (n ω),
      a' ω i *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  have heq : ∀ᵐ ω ∂P, G ω = G' ω := by
    filter_upwards [ha] with ω hω
    dsimp [G, G', a']
    apply Finset.sum_congr rfl
    intro i _
    simp [max_eq_right (hω i)]
  dsimp only at h ⊢
  change (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) = 0 at h
  calc
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      exact congrArg ENNReal.ofReal hω
    _ = 0 := h
