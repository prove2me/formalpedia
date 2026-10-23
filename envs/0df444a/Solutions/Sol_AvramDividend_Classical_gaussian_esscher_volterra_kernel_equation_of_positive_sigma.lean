-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_volterra_kernel_equation_of_positive_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:17:39.158825+00:00
-- url     : https://prove2.me/submissions/7ac8e8d7-4976-4662-bf42-a21c9c2e3a0f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) := by
  let a : ℝ := X.σ ^ 2 / 2
  let β : ℝ :=
    X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y)))
  let K : ℝ → ℝ := fun t : ℝ =>
    (∫⁻ z : ℝ,
      if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
      else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (pow_pos hσ 2) (by norm_num)
  have hK : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    exact gaussian_native_levy_esscher_double_tail_integrable X φ hφ
  have hEq : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x := by
    exact gaussian_esscher_canonical_volterra_identity_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV a β K rfl rfl rfl
  exact ⟨a, β, K, ha, hK, hEq⟩
