-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_constant_rotation_growth
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T19:06:57.732838+00:00
-- url     : https://prove2.me/submissions/c443d19a-ecdd-4e9e-950f-d34ddf0f70bc

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_spectral_splitting
import Theorems.Thm_BirkhoffGlobalSection_saddle_center_angle_linear_growth

open BirkhoffGlobalSection

set_option autoImplicit false

theorem solution (R : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ,
      ∃ (Φ₀ : ℝ → (Phase →L[ℝ] Phase)) (α₀ : ℝ → ℝ),
        Φ₀ a = ContinuousLinearMap.id ℝ Phase ∧
        (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
          HasDerivAt (fun τ => Φ₀ τ v)
            (TangentialHessian.qI.mulVec
              ((!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] :
                Matrix (Fin 4) (Fin 4) ℝ).mulVec (Φ₀ t v))) t) ∧
        ContinuousOn α₀ (Set.Icc a (a + L)) ∧
        (∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
          ambientRotationDet (Φ₀ t) = ⟨ρ * Real.cos (α₀ t), ρ * Real.sin (α₀ t)⟩) ∧
        R < α₀ (a + L) - α₀ a := by
  obtain ⟨ω, lam, hω, hlam, e₁, e₂, f₁, f₂, he₁, he₂, hf₁, hf₂, hindep⟩ :=
    saddle_center_spectral_splitting
  obtain ⟨c₀, hc₀, C₀, hgrowth⟩ :=
    saddle_center_angle_linear_growth ω lam hω hlam e₁ e₂ f₁ f₂
      he₁ he₂ hf₁ hf₂ hindep
  refine ⟨(|R| + |C₀| + 1) / c₀, by positivity, fun a => ?_⟩
  obtain ⟨Φ₀, α₀, hid, hode, hcont, hang, hgrow⟩ :=
    hgrowth a ((|R| + |C₀| + 1) / c₀)
  refine ⟨Φ₀, α₀, hid, hode, hcont, hang, ?_⟩
  have hne0 : c₀ ≠ 0 := ne_of_gt hc₀
  have key : c₀ * ((|R| + |C₀| + 1) / c₀) = |R| + |C₀| + 1 := by field_simp
  have hR : R ≤ |R| := le_abs_self R
  have hC : C₀ ≤ |C₀| := le_abs_self C₀
  rw [key] at hgrow
  linarith
