-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_strict_pos_of_eventual_psi_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:06:51.248894+00:00
-- url     : https://prove2.me/submissions/5fd19653-7bc6-462e-87d7-b5c4543c7a1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_quadratic_laplace

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (β0 C : ℝ) (hβ0 : 0 ≤ β0)
    (hψ : ∀ θ : ℝ, β0 ≤ θ → q < X.ψ θ)
    (hquadratic : ∀ θ : ℝ, β0 ≤ θ →
      X.ψ θ - q ≤ C * (1 + θ ^ 2)) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  have hLap :
      ∀ β : ℝ, β0 ≤ β →
        0 < X.ψ β - q ∧
        IntegrableOn
          (fun x : ℝ => Real.exp (-β * x) * W x)
          (Ioi 0) ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * W x) =
          (X.ψ β - q)⁻¹ := by
    intro β hβ
    have hψβ : q < X.ψ β := hψ β hβ
    have hβnn : 0 ≤ β := le_trans hβ0 hβ
    have hp := hW.2.2.2.2 β hβnn hψβ
    refine ⟨sub_pos.mpr hψβ, ?_, ?_⟩
    · simpa only [neg_mul] using hp.1
    · simpa only [neg_mul] using hp.2
  exact scaleFunction_strict_pos_of_quadratic_laplace
    W X.ψ q β0 C hW.2.1 hW.2.2.2.1 hLap hquadratic
