-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_cumulative_of_exit_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:20:18.3139+00:00
-- url     : https://prove2.me/submissions/9f58799a-a2ba-49a8-a399-cee0f2dcff0c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_positive_esscher_shift_laplace_domain
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_laplace_of_monotone
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The remaining Gaussian fluctuation input is precisely the first-passage exponential bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (hzero : W 0 = 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdecay : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x ≤ Real.exp (-φ * (y - x)) * W y) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  obtain ⟨β₀, C, hβ₀, hC, hψevent⟩ :=
    psi_eventually_positive_quadratic_of_gaussian X q hσ
  have htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ (hdecay φ hφ hroot)
  have hψpos : ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
    intro θ hθ
    exact (hψevent θ hθ).1
  have hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ) :=
    positive_esscher_shift_laplace_domain X.ψ q φ β₀ hφ hψpos
  exact esscher_cumulative_laplace_of_monotone
    X q W hW hzero φ hφ hpos htilt hcut
