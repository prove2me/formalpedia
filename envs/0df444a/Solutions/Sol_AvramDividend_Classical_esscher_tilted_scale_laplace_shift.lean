-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_scale_laplace_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:49:09.043135+00:00
-- url     : https://prove2.me/submissions/4500617b-bfb9-4b52-805d-6e41044d6d83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact Esscher-Laplace shift directly from IsScaleFunction, no change of law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ θ : ℝ) (hθ : 0 ≤ θ + φ) (hψ : q < X.ψ (θ + φ)) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) * (Real.exp (-(φ * y)) * W y))
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
       (Real.exp (-(φ * y)) * W y) ∂volume) =
      (X.ψ (θ + φ) - q)⁻¹ := by
  have hfun :
      (fun y : ℝ => Real.exp (-(θ * y)) * (Real.exp (-(φ * y)) * W y)) =
        (fun y : ℝ => Real.exp (-((θ + φ) * y)) * W y) := by
    funext y
    calc
      Real.exp (-(θ * y)) * (Real.exp (-(φ * y)) * W y) =
          (Real.exp (-(θ * y)) * Real.exp (-(φ * y))) * W y := by ring
      _ = Real.exp (-(θ * y) + -(φ * y)) * W y := by
        rw [Real.exp_add]
      _ = Real.exp (-((θ + φ) * y)) * W y := by
        congr 1
        ring
  have hbase := hW.2.2.2.2 (θ + φ) hθ hψ
  simpa only [hfun] using hbase
