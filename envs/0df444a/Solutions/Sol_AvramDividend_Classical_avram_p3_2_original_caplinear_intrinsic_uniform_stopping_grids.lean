-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:45:39.996197+00:00
-- url     : https://prove2.me/submissions/6aecc1af-6c9a-42d6-a521-d64e963cffd6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One original intrinsic-jump event simultaneously controls every physical
monotone tagged grid and every path-dependent stopping map, including capped
contact and ruin/horizon localisation. No optional stopping identity is used. -/
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
    (q : ℝ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
          (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
          (∑ i : Fin n,
            Real.exp (-(q * (u i : ℝ))) *
              (V (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))) -
               V (riskProcess X x D (u i) ω))) ≤ 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hTop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro h z
    simp [V, h]
  have hFinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro h z
    simp [V, h]
  have hMon : Monotone V :=
    avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
      C hC w V hw_cont hw0 hw_neg hw_smooth hw_grad hTop hFinite
  have hSource :=
    avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
      X hBV x D V hMon q
  dsimp only at hSource ⊢
  filter_upwards [hSource] with ω hω
  obtain ⟨R0, hRdef, hRmono, _, hSign⟩ := hω
  let R : ℝ≥0 → ℝ := fun t =>
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' s : ℝ≥0,
        if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
        else 0).toReal
  have hEq : R0 = R := by
    funext t
    exact hRdef t
  rw [hEq] at hRmono hSign
  exact ⟨hRmono, hSign⟩
