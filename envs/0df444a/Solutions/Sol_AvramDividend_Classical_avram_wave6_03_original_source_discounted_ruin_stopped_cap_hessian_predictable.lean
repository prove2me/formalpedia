-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:28:30.679356+00:00
-- url     : https://prove2.me/submissions/1c3323c4-d8aa-4cf6-b368-eb6d14f15442

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyPredictable_inclusive_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) := by
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0
  have hG : IsStronglyPredictable 𝓕.rightCont G :=
    avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
      X x D hD w C hw
  let B : ℝ≥0 → Ω → ℝ := fun t _ => Real.exp (-(q * (t : ℝ)))
  have hBadapt : StronglyAdapted 𝓕.rightCont B := by
    intro t
    exact stronglyMeasurable_const
  have hBcont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => B s ω) (Iic t) t := by
    intro ω t
    dsimp [B]
    fun_prop
  have hBpred : IsStronglyPredictable 𝓕.rightCont B :=
    avram_wave3_04_strongAdapted_leftContinuous_predictable hBadapt hBcont
  have hDisc : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Real.exp (-(q * (t : ℝ))) * G t ω) :=
    hBpred.mul hG
  have hStop := ruinTime_stopping_rightCont_filtration X x D hD
  have hSurvive :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable
      (ruinTime X x D) hStop
  change IsStronglyPredictable 𝓕.rightCont
    (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) * G t ω) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0)
  exact avram_wave3_04_stronglyPredictable_inclusive_horizon
    (fun t ω =>
      (Real.exp (-(q * (t : ℝ))) * G t ω) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0))
    (hDisc.mul hSurvive) T
