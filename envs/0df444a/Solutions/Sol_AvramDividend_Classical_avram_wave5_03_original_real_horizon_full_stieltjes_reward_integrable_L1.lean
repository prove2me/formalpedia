-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:52.254123+00:00
-- url     : https://prove2.me/submissions/df721bba-22f2-4b9d-a42a-03918dfda626

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ) :
    Integrable (fun ω : Ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  let τ : Ω → ℝ≥0∞ := ruinTime X x D
  let E : Ω → Set ℝ := fun ω => paymentTimes (τ ω) ∩ Iic T
  let wq : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (-(q * s)))
  let S : Set (ℝ × Ω) :=
    {p | p.1 ∈ paymentTimes (τ p.2) ∧ p.1 ≤ T}
  have hτ : Measurable τ := ruinTime_measurable X x D hD.1.1
  have hS : MeasurableSet S :=
    (paymentTimes_joint_measurable τ hτ).inter
      (measurableSet_le measurable_fst measurable_const)
  have hE (ω : Ω) : MeasurableSet (E ω) :=
    (paymentTimes_measurable (τ ω)).inter measurableSet_Iic
  have hwq : Measurable wq :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).neg))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD.1.1
  letI : IsSFiniteKernel κ := hκs
  have hR : Measurable (fun ω : Ω =>
      ∫⁻ s in E ω, wq s ∂(dividendMeasure D ω)) := by
    have hm := measurable_random_indicator_lintegral κ S hS wq hwq
    have heq : (fun ω : Ω =>
        ∫⁻ s in E ω, wq s ∂(dividendMeasure D ω)) =
        (fun ω : Ω =>
          ∫⁻ s, if (s, ω) ∈ S then wq s else 0 ∂κ ω) := by
      funext ω
      rw [hκ ω]
      rw [← lintegral_indicator (hE ω) wq]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ E ω
      · have hsS : (s, ω) ∈ S := by exact hs
        simp [Set.indicator, hs, hsS]
      · have hsS : (s, ω) ∉ S := by
          intro h
          exact hs h
        simp [Set.indicator, hs, hsS]
    rw [heq]
    simpa only [S, Set.mem_setOf_eq] using hm
  have hMoment :=
    avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
      X x C D hD T hT q
  have hK : ENNReal.ofReal
      (Real.exp (|X.ψ 1 - q| * (((T.toNNReal + 1 : ℝ≥0) : ℝ)))) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hx : ENNReal.ofReal (Real.exp x) < ⊤ :=
    ENNReal.ofReal_lt_top
  have hfinite :
      (∫⁻ ω, ∫⁻ s in E ω, wq s
        ∂(dividendMeasure D ω) ∂P) < ⊤ :=
    lt_of_le_of_lt hMoment (ENNReal.mul_lt_top hK hx)
  change Integrable (fun ω : Ω =>
    (∫⁻ s in E ω, wq s ∂(dividendMeasure D ω)).toReal) P
  exact integrable_toReal_of_lintegral_ne_top hR.aemeasurable hfinite.ne
