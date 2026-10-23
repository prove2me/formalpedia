-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_scale_laplace_of_positive_agreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:01:45.91991+00:00
-- url     : https://prove2.me/submissions/2b4d3fc9-d1b6-463b-a880-77c5795d88ea

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An arbitrary positive-half-line representative has the canonical Esscher Laplace transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ θ : ℝ) (hθ : 0 ≤ θ + φ) (hψ : q < X.ψ (θ + φ))
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y)
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
      (X.ψ (θ + φ) - q)⁻¹ := by
  obtain ⟨hi, he⟩ :=
    esscher_tilted_scale_laplace_shift X q W hW φ θ hθ hψ
  have hEq : EqOn
      (fun y : ℝ => Real.exp (-(θ * y)) * V y)
      (fun y : ℝ => Real.exp (-(θ * y)) *
        (Real.exp (-(φ * y)) * W y))
      (Ioi (0 : ℝ)) := by
    intro y hy
    simpa only using
      congrArg (fun t : ℝ => Real.exp (-(θ * y)) * t) (hV y hy)
  constructor
  · exact hi.congr_fun hEq.symm measurableSet_Ioi
  · calc
      (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
          ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
            (Real.exp (-(φ * y)) * W y) ∂volume :=
            setIntegral_congr_fun measurableSet_Ioi hEq
      _ = (X.ψ (θ + φ) - q)⁻¹ := he
