-- Prove2me | solution 1 for AvramDividend.Classical.esscher_cumulative_laplace_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:45:59.588508+00:00
-- url     : https://prove2.me/submissions/6f1b0185-c624-41d2-981b-99ac277aa230

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_positive_cumulative_of_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A monotone Esscher tilt with a Laplace-domain cutoff has a cumulative measure representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (φ : ℝ) (hφ : 0 < φ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ)) :
    ∃ (β : Measure ℝ) (φ' b : ℝ),
      0 < φ' ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ' * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ' * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by
  rcases hcut with ⟨b, hb⟩
  rcases esscher_tilt_positive_cumulative_of_monotone
      X q W hW hzero φ hpos htilt with
    ⟨β, hβ, hfin, hposβ⟩
  have hnonneg : ∀ x : ℝ, 0 ≤ Real.exp (-φ * x) * W x := by
    intro x
    have hWnonneg : 0 ≤ W x := by
      by_cases hx : x < 0
      · rw [hW.1 x hx]
      · exact hW.2.1 x (le_of_not_gt hx)
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hWnonneg
  refine ⟨β, φ, b, hφ, hfin, hposβ, ?_⟩
  intro θ hθ
  have hdom := hb θ hθ
  have hWlap := hW.2.2.2.2 (θ + φ) hdom.1 hdom.2
  have hexp : ∀ x : ℝ,
      Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
        Real.exp (-((θ + φ) * x)) * W x := by
    intro x
    calc
      Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
          (Real.exp (-θ * x) * Real.exp (-φ * x)) * W x := by ring
      _ = Real.exp ((-θ * x) + (-φ * x)) * W x := by rw [Real.exp_add]
      _ = Real.exp (-((θ + φ) * x)) * W x := by congr 1; ring
  have hF : (fun x : ℝ =>
      Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) =
      (fun x : ℝ => Real.exp (-((θ + φ) * x)) * W x) :=
    funext hexp
  have hG : (fun x : ℝ =>
      Real.exp (-θ * x) * (β (Iic x)).toReal) =
      (fun x : ℝ =>
        Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) := by
    funext x
    rw [hβ x, ENNReal.toReal_ofReal (hnonneg x)]
  constructor
  · rw [hF]
    exact hWlap.1
  constructor
  · rw [hG, hF]
    exact hWlap.1
  · rw [hG]
