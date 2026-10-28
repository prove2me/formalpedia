-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_unit_cash_measurable_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:32:43.850729+00:00
-- url     : https://prove2.me/submissions/c6c57f7a-10e7-4cd9-84cb-c4ddc29ef1bd

import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Exact stopped discounted unit-interval Stieltjes cash is a measurable
    random variable, including continuous payments and right-jump atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) (k : ℕ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  obtain ⟨κ, hsf, hκ⟩ :=
    AvramDividend.Classical.dividendMeasure_global_sfinite_kernel_exists D hD
  letI : ProbabilityTheory.IsSFiniteKernel κ := hsf
  have hτ : Measurable (ruinTime X x D) :=
    AvramDividend.Classical.ruinTime_measurable X x D hD
  have hw : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * t)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  let S : Set (ℝ × Ω) := {p | p.1 ∈
    (paymentTimes (ruinTime X x D p.2) ∩ Iic (T : ℝ)) ∩
      Ico (k : ℝ) ((k : ℝ) + 1)}
  have hS : MeasurableSet S := by
    have hP :=
      AvramDividend.Classical.paymentTimes_joint_measurable
        (ruinTime X x D) hτ
    have hT : MeasurableSet
        {p : ℝ × Ω | p.1 ∈ Iic (T : ℝ)} :=
      measurableSet_Iic.preimage measurable_fst
    have hK : MeasurableSet
        {p : ℝ × Ω | p.1 ∈ Ico (k : ℝ) ((k : ℝ) + 1)} :=
      measurableSet_Ico.preimage measurable_fst
    change MeasurableSet
      (({p : ℝ × Ω | p.1 ∈ paymentTimes (ruinTime X x D p.2)} ∩
        {p : ℝ × Ω | p.1 ∈ Iic (T : ℝ)}) ∩
        {p : ℝ × Ω | p.1 ∈ Ico (k : ℝ) ((k : ℝ) + 1)})
    exact (hP.inter hT).inter hK
  have hm := AvramDividend.Classical.measurable_random_indicator_lintegral
    κ S hS (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) hw
  convert hm using 1
  funext ω
  have hsω : MeasurableSet
      ((paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
        Ico (k : ℝ) ((k : ℝ) + 1)) :=
    ((AvramDividend.Classical.paymentTimes_measurable
      (ruinTime X x D ω)).inter measurableSet_Iic).inter measurableSet_Ico
  rw [hκ ω]
  rw [← lintegral_indicator (μ := dividendMeasure D ω) hsω]
  apply lintegral_congr
  intro t
  have hiff : (t, ω) ∈ S ↔
      t ∈ (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
        Ico (k : ℝ) ((k : ℝ) + 1) := Iff.rfl
  by_cases ht : t ∈ (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
      Ico (k : ℝ) ((k : ℝ) + 1)
  · have hp : (t, ω) ∈ S := hiff.mpr ht
    simp [Set.indicator, ht, hp]
  · have hp : (t, ω) ∉ S := fun hp => ht (hiff.mp hp)
    simp [Set.indicator, ht, hp]
