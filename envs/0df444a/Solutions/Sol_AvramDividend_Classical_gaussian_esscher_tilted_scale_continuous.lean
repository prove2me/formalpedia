-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_tilted_scale_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:01:40.318986+00:00
-- url     : https://prove2.me/submissions/11bfd172-bcb2-435f-bb98-a7dc9ad92c94

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Gaussian origin criterion and exponential continuity give a continuous Esscher tilt. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContinuousOn V (Ioi (0 : ℝ)) := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hWcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have htiltCont : Continuous (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    fun_prop
  apply htiltCont.continuousOn.congr
  intro x hx
  exact hV x hx
