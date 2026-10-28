-- Prove2me | solution 1 for AvramDividend.Classical.levy_esscher_root_scale_tilted_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:13:29.358797+00:00
-- url     : https://prove2.me/submissions/0350420f-a132-4afc-9093-8e1edd25b766

import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(β * y)) * (Real.exp (-(φ * y)) * W y))
      (Ioi 0) volume ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(β * y)) *
      (Real.exp (-(φ * y)) * W y) ∂volume) =
      (X.ψ (φ + β) - q)⁻¹ := by
  have hn : 0 ≤ β + φ := le_of_lt (add_pos hβ hφ)
  have hd : q < X.ψ (β + φ) := by
    simpa only [add_comm] using
      (levy_psi_root_strictly_above_shift
        X q φ β hq hφ hβ hroot)
  have h := esscher_tilted_scale_laplace_shift
    X q W hW φ β hn hd
  convert h using 1 <;> simp only [add_comm]
