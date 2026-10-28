-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_tilt_vanishes_right_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:54:10.015258+00:00
-- url     : https://prove2.me/submissions/223a509f-938d-4441-b37a-2f97d30ec89f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Exponential tilting preserves the zero-origin right limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hWc : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hCont : Continuous (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    fun_prop
  have ht : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [hzero] using (hCont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hV x hx).symm
