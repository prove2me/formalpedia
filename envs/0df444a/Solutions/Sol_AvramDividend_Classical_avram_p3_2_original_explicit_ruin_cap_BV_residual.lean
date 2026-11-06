-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_explicit_ruin_cap_BV_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:46:34.458299+00:00
-- url     : https://prove2.me/submissions/2e7c96c7-35a7-47e7-8c3b-4d0aafd0f6a7

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

/-- Explicit original intrinsic BV downward residual, on the actual ruin-clipped
physical grid; retains its original compensated-jump definition for later L1 use. -/
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
    (q : ℝ) (T : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u i) τ
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0,
            if 0 < s ∧ s ≤ t then
              ENNReal.ofReal
                (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        (∑ i : Fin n,
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by
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
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let v : ℕ → ℝ≥0 := fun i => min (u i) τ
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
  refine ⟨hRmono, ?_⟩
  have hvmono : Monotone v := by
    intro i j hij
    exact min_le_min (hu hij) le_rfl
  have hvstop : v n ≤ τ := min_le_right _ _
  exact hSign (fun _ => τ) v hvmono n hvstop
