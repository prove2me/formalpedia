-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_random_length_positive_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:08:39.463495+00:00
-- url     : https://prove2.me/submissions/ae43576a-707a-4a25-8c87-8b21f038c5d1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Even a path-dependent original-X physical grid of path-dependent length,
localised at a potentially random clock, has no positive expected intrinsic downward nonlinear correction.
This holds without a separate L1 or predictability assumption on the grid. -/
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
    (n : Ω → ℕ) (hstop : ∀ ω, u ω (n ω) ≤ τ ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := u ω
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
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  let G : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := u ω
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
  dsimp only at h ⊢
  have hNonpos : ∀ᵐ ω ∂P, G ω ≤ 0 := by
    filter_upwards [h] with ω hω
    exact hω.2 τ (u ω) (hu ω) (n ω) (hstop ω)
  have hZero : (fun ω => ENNReal.ofReal (G ω)) =ᵐ[P]
      (fun _ : Ω => (0 : ℝ≥0∞)) := by
    filter_upwards [hNonpos] with ω hω
    exact ENNReal.ofReal_eq_zero.mpr hω
  calc
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
        ∫⁻ _ω : Ω, (0 : ℝ≥0∞) ∂P := lintegral_congr_ae hZero
    _ = 0 := by simp
