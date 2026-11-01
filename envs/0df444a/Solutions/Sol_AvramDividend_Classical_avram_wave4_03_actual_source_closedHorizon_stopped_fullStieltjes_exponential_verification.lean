-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:06:50.732426+00:00
-- url     : https://prove2.me/submissions/dd955c0c-ac02-4521-81dd-fb53ef05a9ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
/-- Original-source stopped [0,T] discounted cash budget, including initial Stieltjes atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      if s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by
  classical
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp x)
  let g : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
      rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
  have hgm (ω : Ω) : Measurable (g ω) := by
    have hjoint := avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
      X 0 D hD.1.1 1 (X.ψ 1)
    have htime : Measurable (fun s : ℝ => (s.toNNReal, ω)) :=
      measurable_real_toNNReal.prodMk measurable_const
    have h := (hjoint.comp htime).ennreal_ofReal
    simpa only [g, Function.comp_def, one_mul, zero_add] using h
  have hgo : Measurable (fun ω : Ω =>
      ∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
    have hS : MeasurableSet {z : ℝ × Ω | z.1 ∈ Icc (0 : ℝ) (T : ℝ)} := measurableSet_Icc.preimage measurable_fst
    have h := avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
      X 0 D hD.1.1 1 (X.ψ 1) _ hS
    have h' : Measurable (fun ω : Ω =>
        ∫⁻ s : ℝ, if s ∈ Icc (0 : ℝ) (T : ℝ) then g ω s
          else 0 ∂dividendMeasure D ω) := by
      simpa only [g, one_mul, zero_add, Set.mem_setOf_eq] using h
    have heq :
        (fun ω : Ω => ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
          g ω s ∂dividendMeasure D ω) =
        (fun ω : Ω => ∫⁻ s : ℝ,
          if s ∈ Icc (0 : ℝ) (T : ℝ) then g ω s else 0
          ∂dividendMeasure D ω) := by
      funext ω
      rw [← lintegral_indicator measurableSet_Icc (g ω)]
      simp only [Set.indicator_apply]
    rw [heq]
    exact h'
  have hpoint (ω : Ω) (s : ℝ) :
      (if s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
       else 0) ≤ c * g ω s := by
    by_cases hp : s ∈ paymentTimes (ruinTime X x D ω)
    · have hs : 0 ≤ s := by
        change 0 ≤ s ∧ (s = 0 ∨ ENNReal.ofReal s < ruinTime X x D ω) at hp
        exact hp.1
      have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs
      have hp' : (s.toNNReal : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by
        simpa only [hs'] using hp
      have hr := avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
        X x C D hD ω s.toNNReal hp' (X.ψ 1)
      simp only [if_pos hp, c, g]
      simpa only [ENNReal.ofReal_mul (Real.exp_nonneg x)] using
        (ENNReal.ofReal_le_ofReal hr)
    · simp only [if_neg hp, zero_le]
  have hinner (ω : Ω) :
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        else 0 ∂dividendMeasure D ω) ≤
      c * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
    calc
      _ ≤ ∫⁻ s in Icc (0 : ℝ) (T : ℝ), c * g ω s ∂dividendMeasure D ω :=
        lintegral_mono (hpoint ω)
      _ = c * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
        rw [lintegral_const_mul]
        exact hgm ω
  have hsource : (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      g ω s ∂dividendMeasure D ω ∂P) ≤ 1 := by
    simpa only [g] using
      (avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget X D hD.1.1 T hT)
  calc
    _ ≤ ∫⁻ ω, c * (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        g ω s ∂dividendMeasure D ω) ∂P := lintegral_mono hinner
    _ = c * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        g ω s ∂dividendMeasure D ω ∂P) := by
      rw [lintegral_const_mul]
      exact hgo
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = ENNReal.ofReal (Real.exp x) := by simp only [c, mul_one]
