-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:22:03.539131+00:00
-- url     : https://prove2.me/submissions/d4377198-4b9b-48f4-a4cd-b6cac85186e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Original strict-survival killed terminal is jointly measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if (z.1 : ℝ≥0∞) < ruinTime X x D z.2 then
        max 0 (Real.exp (-(q * (z.1 : ℝ))) *
          w (x + X.X z.1 z.2 - rightLimit D z.1 z.2))
      else 0) := by
  have hYexp : Measurable (fun z : ℝ≥0 × Ω =>
      Real.exp ((1 : ℝ) *
        (x + X.X z.1 z.2 - rightLimit D z.1 z.2) -
        (z.1 : ℝ) * (0 : ℝ))) :=
    avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
      X x D hD 1 0
  have hY : Measurable (fun z : ℝ≥0 × Ω =>
      x + X.X z.1 z.2 - rightLimit D z.1 z.2) := by
    simpa only [one_mul, mul_zero, sub_zero, Real.log_exp] using
      hYexp.log
  have hTReal : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hTENN : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr measurable_fst
  have hRuin : Measurable
      (fun z : ℝ≥0 × Ω => ruinTime X x D z.2) :=
    (ruinTime_measurable X x D hD).comp measurable_snd
  have hSurv : MeasurableSet
      {z : ℝ≥0 × Ω | (z.1 : ℝ≥0∞) < ruinTime X x D z.2} :=
    measurableSet_lt hTENN hRuin
  have hw : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw_cont hw_neg).1
  have hExp : Measurable (fun z : ℝ≥0 × Ω =>
      Real.exp (-(q * (z.1 : ℝ)))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hTReal).neg)
  have hPositive : Measurable (fun z : ℝ≥0 × Ω =>
      max 0 (Real.exp (-(q * (z.1 : ℝ))) *
        w (x + X.X z.1 z.2 - rightLimit D z.1 z.2))) :=
    measurable_const.max (hExp.mul (hw.comp hY))
  exact Measurable.ite hSurv hPositive measurable_const
