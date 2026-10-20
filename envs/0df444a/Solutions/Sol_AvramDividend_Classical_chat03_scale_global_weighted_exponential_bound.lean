-- Prove2me | solution 1 for AvramDividend.Classical.chat03_scale_global_weighted_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:06:38.914476+00:00
-- url     : https://prove2.me/submissions/c9b87f70-6a85-44a6-af6f-09c5716a784d

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_laplace_pointwise_envelope
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Extend the Proved scale Laplace envelope to every real reserve, including
negative reserves where the canonical scale function is exactly zero.
This is needed to bound stochastic stopped reserves that may overshoot ruin.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) :
    Real.exp (-(θ * (y + 1))) * W y ≤ (X.ψ θ - q)⁻¹ := by
  by_cases hy : 0 ≤ y
  · exact chat03_scale_laplace_pointwise_envelope X q W hW θ y hθ hψ hy
  · have hneg : y < 0 := lt_of_not_ge hy
    rw [hW.1 y hneg]
    simp only [mul_zero]
    exact inv_nonneg.mpr (sub_nonneg.mpr hψ.le)