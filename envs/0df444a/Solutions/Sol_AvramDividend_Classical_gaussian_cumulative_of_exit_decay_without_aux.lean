-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_cumulative_of_exit_decay_without_aux
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:30:02.51221+00:00
-- url     : https://prove2.me/submissions/69fbeddb-7717-46f9-b260-d1bfcc295601

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_cumulative_of_exit_decay
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The Gaussian case supplies positivity and zero-origin automatically for the Esscher measure bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
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
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing
      X q hq W hW hσ
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_gaussian X q W hW hσ x hx
  exact gaussian_esscher_cumulative_of_exit_decay
    X q hq W hW hσ hzero hpos hdecay
