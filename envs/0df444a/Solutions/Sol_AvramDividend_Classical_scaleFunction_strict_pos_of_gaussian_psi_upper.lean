-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_gaussian_psi_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:46:27.174001+00:00
-- url     : https://prove2.me/submissions/d6f7a2f6-8754-4620-b2b7-8f042189a9b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian_jump_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn (fun y : ℝ =>
        Real.exp (θ * y) - 1 -
          θ * y * ((Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y)) (Iio (0 : ℝ)) X.ν)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ θ : ℝ, 1 ≤ θ → X.ψ θ ≤ C * θ ^ 2) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  obtain ⟨β0, hβ0, hψ⟩ :=
    psi_eventually_gt_of_gaussian_jump_integrable
      X q hσ hν hjump
  let β1 : ℝ := max 1 β0
  have hβ1 : 0 ≤ β1 := by
    dsimp [β1]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (le_max_left (1 : ℝ) β0)
  have hψ1 : ∀ θ : ℝ, β1 ≤ θ → q < X.ψ θ := by
    intro θ hθ
    exact hψ θ ((le_max_right (1 : ℝ) β0).trans hθ)
  have hquad : ∀ θ : ℝ, β1 ≤ θ →
      X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
    intro θ hθ
    have ht1 : 1 ≤ θ :=
      (le_max_left (1 : ℝ) β0).trans hθ
    have hu := hupper θ ht1
    nlinarith
  exact scaleFunction_strict_pos_of_eventual_psi_bound
    X q W hW β1 C hβ1 hψ1 hquad
