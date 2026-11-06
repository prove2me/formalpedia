-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_j_original_actual_stop_discount_raw_large_mark_L1_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:23:13.068973+00:00
-- url     : https://prove2.me/submissions/35c7ebf4-0629-49c7-82f1-3d280f248bd3

import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_raw_large_mark_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Literal original X/D survival-killed and discounted large-negative-mark
jump generator is L1 under an explicitly bounded alive reserve strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hStoppedReserveCap : ∀ p : ℝ≥0 × Ω,
      (p.1 : ℝ≥0∞) ≤ τ p.2 →
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc 0 v)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    [IsFiniteMeasure μ] :
    (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
     let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1;
     Integrable
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Y p.1 + p.2) - w (Y p.1))
        else 0)
      (μ.prod (X.ν.restrict (Iio (-ε))))) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod inferInstance
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1
  have hY : Measurable Y :=
    (avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
      X x D hD).measurable
  have hStop : Measurable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) :=
    (avram_wave3_04_inclusiveSurvival_stronglyPredictable
      τ hτ).measurable
  let A : Set (ℝ≥0 × Ω) := {p | (p.1 : ℝ≥0∞) ≤ τ p.2}
  have hA : MeasurableSet A := by
    have hpre := hStop (measurableSet_singleton (1 : ℝ))
    convert hpre using 1
    ext p
    by_cases hp : (p.1 : ℝ≥0∞) ≤ τ p.2 <;> simp [A, hp]
  let a : ℝ≥0 × Ω → ℝ :=
    fun p => Real.exp (-(q * (p.1 : ℝ)))
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
  have ha : Measurable a := hBpred.measurable
  have hcap : ∀ p ∈ A, Y p ∈ Icc 0 v := by
    intro p hp
    exact hStoppedReserveCap p hp
  have hweight : ∀ p, |a p| ≤ (1 : ℝ) := by
    intro p
    have hn : 0 ≤ q * (p.1 : ℝ) :=
      mul_nonneg hq (NNReal.coe_nonneg _)
    have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      calc
        Real.exp (-(q * (p.1 : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (neg_nonpos.mpr hn)
        _ = 1 := Real.exp_zero
    simpa only [a, abs_of_pos (Real.exp_pos _)] using he
  have hBig :=
    avram_p4_c_generator_localised_weighted_raw_large_mark_L1
      X μ Y a hY ha A hA w v ε hv hε hw_cont hw_neg
      hcap (1 : ℝ) hweight
  let F : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))
    else 0
  have hfun :
      ({p : ((ℝ≥0 × Ω) × ℝ) | p.1 ∈ A}.indicator
        (fun p => a p.1 * (w (Y p.1 + p.2) - w (Y p.1)))) = F := by
    funext p
    by_cases hp : (p.1.1 : ℝ≥0∞) ≤ τ p.1.2
    · simp [Set.indicator_apply, A, a, F, hp]
    · simp [Set.indicator_apply, A, a, F, hp]
  change Integrable F (μ.prod (X.ν.restrict (Iio (-ε))))
  rw [← hfun]
  exact hBig
