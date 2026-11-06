-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_inclusive_stopped_discounted_taylor_joint_predictable_mark_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:26:35.383207+00:00
-- url     : https://prove2.me/submissions/65b5cc1b-42b5-4089-b272-9c85adfa7480

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same-original stopped discounted nonlinear Taylor kernel jointly
measurable in physical predictable time-path and real Lévy mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (q : ℝ)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        ((if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) *
          Real.exp (-(q * (p.1.1 : ℝ)))) *
          ((fun y : ℝ => w (y + p.2) - w y - p.2 * deriv w y)
            (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.1.2 -
                rightLimit D s p.1.2) p.1.1))) := by
  have hJ :=
    avram_p4_s3_interval_i_original_physical_prejump_taylor_joint_predictable_mark_measurable
      X x D hD w hw
  have hSurv : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) :=
    avram_wave3_04_inclusiveSurvival_stronglyPredictable τ hτ
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
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod inferInstance
  have hSP : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) :=
    hSurv.measurable.comp measurable_fst
  have hBP : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      Real.exp (-(q * (p.1.1 : ℝ)))) :=
    hBpred.measurable.comp measurable_fst
  exact (hSP.mul hBP).mul hJ
