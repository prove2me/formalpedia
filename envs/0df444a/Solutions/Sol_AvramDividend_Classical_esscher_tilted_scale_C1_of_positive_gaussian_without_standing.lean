-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_scale_C1_of_positive_gaussian_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:01:45.620992+00:00
-- url     : https://prove2.me/submissions/bb99614c-05be-4ae1-a396-0a5e06de3896

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_integrated_volterra_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Gaussian regularity via a tilted-scale integrated Volterra resolvent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hWcont : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have htiltCont :
      Continuous (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
    fun_prop
  have hVcont : ContinuousOn V (Ioi (0 : ℝ)) := by
    apply htiltCont.continuousOn.congr
    intro x hx
    exact hV x hx
  obtain ⟨a, β, K, ha, hK, hVbound, hEq⟩ :=
    gaussian_esscher_integrated_volterra_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  exact integrated_volterra_regularizes_C1
    V K a β ha hK hVcont hVbound hEq
