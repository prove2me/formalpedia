-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_fixed_mark_taylor_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:11:14.591038+00:00
-- url     : https://prove2.me/submissions/31dba346-736c-47b1-8db5-9d3c251d6ba6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped, discounted fixed-mark nonlinear Itô–Meyer Taylor
kernel is predictable in the unchanged physical filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (q z : ℝ)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        (if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) *
          Real.exp (-(q * (t : ℝ))) *
            ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
              (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))) := by
  let B : ℝ≥0 → Ω → ℝ :=
    fun t _ => Real.exp (-(q * (t : ℝ)))
  have hBadapt : StronglyAdapted 𝓕.rightCont B := by
    intro t
    exact stronglyMeasurable_const
  have hBcont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => B s ω) (Iic t) t := by
    intro ω t
    dsimp [B]
    fun_prop
  have hBpred : IsStronglyPredictable 𝓕.rightCont B :=
    avram_wave3_04_strongAdapted_leftContinuous_predictable
      hBadapt hBcont
  have hSurv : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable τ hτ
  have hJ :=
    avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
      X x D hD w hw z
  exact (hSurv.mul hBpred).mul hJ
