-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:33:38.845783+00:00
-- url     : https://prove2.me/submissions/7fb83972-8cf3-4be7-96e7-ac33dde81fc2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_mean_value
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (R : ℝ) (hq : 0 ≤ q)
    (hband : ∀ s : ℝ≥0, s ≤ H → (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      riskProcess X x D s ω ∈ Icc 0 R ∧ x + X.X s ω - rightLimit D s ω ∈ Icc 0 R) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let μ := (dividendMeasure D ω).restrict S
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    let F : ℝ → ℝ := fun t => Real.exp (-(q * t)) *
      (1 - Q (riskProcess X x D t.toNNReal ω)
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω))
    Integrable F μ := by 
  dsimp only
  let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
  let μ := (dividendMeasure D ω).restrict S
  let A : ℝ → ℝ := fun t => riskProcess X x D t.toNNReal ω
  let B : ℝ → ℝ := fun t => x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω
  haveI : IsFiniteMeasure μ := avram_locmoll_band_eligible_measure_finite X x q D hD ω H
  have hp : Measurable (fun t : ℝ => (t.toNNReal, ω)) := Measurable.prodMk measurable_real_toNNReal measurable_const
  have hA : Measurable A := (avram_p3_g2_original_prepayment_riskProcess_joint_measurable X x D hD).comp hp
  have hB : Measurable B := (avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable X x D hD).comp hp
  have hd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hQ : Measurable (fun t => if A t = B t then deriv g (A t) else (g (A t) - g (B t)) / (A t - B t)) :=
    Measurable.ite (measurableSet_eq_fun hA hB) (hd.measurable.comp hA) (((hg.continuous.measurable.comp hA).sub (hg.continuous.measurable.comp hB)).div (hA.sub hB))
  have hE : Measurable (fun t : ℝ => Real.exp (-(q * t))) := by fun_prop
  have hcompact : IsCompact (Icc (0 : ℝ) R) := isCompact_Icc
  obtain ⟨K,hK⟩ := (hcompact.image hd.norm).bddAbove
  refine (integrable_const (1 + max K 0)).mono'
    (hE.mul (measurable_const.sub hQ)).aestronglyMeasurable ?_
  have hm : MeasurableSet S := (avram_p4_d_dividend_original_paymentTimes_measurableSet _).inter measurableSet_Iic
  filter_upwards [ae_restrict_mem hm] with t ht
  have ht0 : 0 ≤ t := ht.1.1
  have htc : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht0
  have hs : t.toNNReal ≤ H := NNReal.coe_le_coe.mp (by rw [htc]; exact ht.2)
  have he : t.toNNReal = 0 ∨ (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
    rcases ht.1.2 with h | h
    · left; simp [h]
    · right; rwa [← ENNReal.ofReal_coe_nnreal, htc]
  obtain ⟨ha,hb⟩ := hband t.toNNReal hs he
  have hBA : B t ≤ A t := by
    have h := dividendStrategy_le_rightLimit D hD ω t.toNNReal
    change x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ≤ x + X.X t.toNNReal ω - D t.toNNReal ω
    linarith
  obtain ⟨z,hz,hzQ⟩ := avram_locmoll_band_secant_mean_value g hg (A t) (B t) hBA
  have hzR : z ∈ Icc 0 R := ⟨hb.1.trans hz.1, hz.2.trans ha.2⟩
  have hnorm : |deriv g z| ≤ max K 0 := (hK ⟨z,hzR,rfl⟩).trans (le_max_left _ _)
  have hdisc : Real.exp (-(q * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  dsimp only at hzQ
  change ‖Real.exp (-(q * t)) * (1 - (if A t = B t then deriv g (A t) else (g (A t) - g (B t)) / (A t - B t)))‖ ≤ _
  rw [← hzQ, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1 * |1 - deriv g z| := mul_le_mul_of_nonneg_right hdisc (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; have hh := abs_sub_le (1 : ℝ) 0 (deriv g z); simp at hh; linarith
