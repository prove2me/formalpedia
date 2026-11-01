-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_source_positiveTime_stopped_exponential_expected_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:02:35.072654+00:00
-- url     : https://prove2.me/submissions/d25c9a95-f6ed-44fe-8ab5-81c6218ece59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
/-- Actual source Lévy expected stopped (0,T] dividend reward, including all Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) ∧ s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by
  classical
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp x)
  let g : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1)) else 0
  have hgm (ω : Ω) : Measurable (g ω) := by
    have hjoint := avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable X 0 D hD.1.1 1 (X.ψ 1)
    have htime : Measurable (fun s : ℝ => (s.toNNReal, ω)) :=
      measurable_real_toNNReal.prodMk measurable_const
    have hbase : Measurable (fun s : ℝ =>
        ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
          rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))) := by
      simpa only [Function.comp_def, one_mul, zero_add] using
        (hjoint.comp htime).ennreal_ofReal
    dsimp only [g]
    exact Measurable.ite measurableSet_Ioc hbase measurable_const
  have hgo : Measurable (fun ω : Ω =>
      ∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω) := by
    have hS : MeasurableSet {z : ℝ × Ω | z.1 ∈ Ioc (0 : ℝ) (T : ℝ)} := measurableSet_Ioc.preimage measurable_fst
    have h := avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable X 0 D hD.1.1 1 (X.ψ 1) _ hS
    simpa only [g, one_mul, zero_add, Set.mem_setOf_eq] using h
  have hpoint (ω : Ω) (s : ℝ) :
      (if s ∈ Ioc (0 : ℝ) (T : ℝ) ∧ s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
       else 0) ≤ c * g ω s := by
    by_cases hs : s ∈ Ioc (0 : ℝ) (T : ℝ)
    · by_cases hp : s ∈ paymentTimes (ruinTime X x D ω)
      · have hp' : (s.toNNReal : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
          simpa only [Real.coe_toNNReal s hs.1.le] using hp
        have hr := avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
          X x C D hD ω s.toNNReal hp' (X.ψ 1)
        have hboth : s ∈ Ioc (0 : ℝ) (T : ℝ) ∧ s ∈ paymentTimes (ruinTime X x D ω) := ⟨hs, hp⟩
        rw [if_pos hboth]
        simp only [c, g, if_pos hs]
        simpa only [ENNReal.ofReal_mul (Real.exp_nonneg x)] using
          (ENNReal.ofReal_le_ofReal hr)
      · have hn : ¬(s ∈ Ioc (0 : ℝ) (T : ℝ) ∧
          s ∈ paymentTimes (ruinTime X x D ω)) := fun h => hp h.2
        simp only [if_neg hn, g, if_pos hs, zero_le]
    · have hn : ¬(s ∈ Ioc (0 : ℝ) (T : ℝ) ∧
        s ∈ paymentTimes (ruinTime X x D ω)) := fun h => hs h.1
      simp only [if_neg hn, g, if_neg hs, mul_zero, le_refl]
  have hinner (ω : Ω) :
      (∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) ∧
        s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        else 0 ∂dividendMeasure D ω) ≤
      c * (∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω) := by
    calc
      _ ≤ ∫⁻ s : ℝ, c * g ω s ∂dividendMeasure D ω := lintegral_mono (hpoint ω)
      _ = c * (∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω) := by
        rw [lintegral_const_mul]
        exact hgm ω
  have hsource : (∫⁻ ω, ∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω ∂P) ≤ 1 := by
    simpa only [g] using (avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget X D hD.1.1 T hT)
  calc
    _ ≤ ∫⁻ ω, c * (∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω) ∂P :=
      lintegral_mono hinner
    _ = c * (∫⁻ ω, ∫⁻ s : ℝ, g ω s ∂dividendMeasure D ω ∂P) := by
      rw [lintegral_const_mul]
      exact hgo
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = ENNReal.ofReal (Real.exp x) := by simp only [c, mul_one]
