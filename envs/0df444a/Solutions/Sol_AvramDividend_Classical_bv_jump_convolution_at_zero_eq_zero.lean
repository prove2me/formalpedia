-- Prove2me | solution 1 for AvramDividend.Classical.bv_jump_convolution_at_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:57:10.174529+00:00
-- url     : https://prove2.me/submissions/594e8ab9-b508-4fd4-a4c7-46b9dd75ccf4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrating a scale function over strictly negative jump sizes gives zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫ y in Iio (0 : ℝ), W y ∂X.ν) = 0 := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  have hneg : ∀ᵐ y : ℝ ∂μ, y < 0 := by
    simpa only [mem_Iio] using
      (ae_restrict_mem (μ := X.ν) measurableSet_Iio)
  have hzero : (fun y : ℝ => W y) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hneg] with y hy
    exact hW.1 y hy
  change (∫ y : ℝ, W y ∂μ) = 0
  calc
    (∫ y : ℝ, W y ∂μ) = ∫ y : ℝ, (0 : ℝ) ∂μ := integral_congr_ae hzero
    _ = 0 := integral_zero ℝ ℝ
