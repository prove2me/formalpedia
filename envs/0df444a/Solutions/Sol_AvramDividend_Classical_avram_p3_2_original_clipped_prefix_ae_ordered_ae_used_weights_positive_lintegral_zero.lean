-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_clipped_prefix_ae_ordered_ae_used_weights_positive_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:09:06.635177+00:00
-- url     : https://prove2.me/submissions/5f662897-f67e-4c17-9f2a-a2b0fd10ac29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The true stopped BV nonlinear correction has zero positive outer mass
even when physical grid ordering and used-weight positivity hold only a.e. -/
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
    (hu : ∀ᵐ ω ∂P, ∀ i, i < n ω → u ω i ≤ u ω (i + 1))
    (ha : ∀ᵐ ω ∂P, ∀ i, i < n ω → 0 ≤ a ω i) :
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
  classical
  let Good : Set Ω := {ω | ∀ i, i < n ω → u ω i ≤ u ω (i + 1)}
  let u' : Ω → ℕ → ℝ≥0 := fun ω j =>
    if ω ∈ Good then u ω j else 0
  have hu' : ∀ ω i, i < n ω → u' ω i ≤ u' ω (i + 1) := by
    intro ω i hi
    by_cases hg : ω ∈ Good
    · have hgi : u ω i ≤ u ω (i + 1) := hg i hi
      simpa [u', hg] using hgi
    · simp [u', hg]
  have h := avram_p3_2_original_clipped_prefix_ae_used_nonnegative_weights_positive_lintegral_zero
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    τ u' n a hu' ha
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
    let v : ℕ → ℝ≥0 := fun i => min (u' ω i) (τ ω)
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
  have heq : ∀ᵐ ω ∂P, G ω = G' ω := by
    filter_upwards [hu] with ω hω
    have hg : ω ∈ Good := hω
    simp [G, G', u', hg]
  dsimp only at h ⊢
  change (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) = 0 at h
  calc
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
        (∫⁻ ω, ENNReal.ofReal (G' ω) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      exact congrArg ENNReal.ofReal hω
    _ = 0 := h
