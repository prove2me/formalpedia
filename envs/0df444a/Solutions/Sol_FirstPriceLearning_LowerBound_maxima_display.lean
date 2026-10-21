-- Prove2me | solution 1 for FirstPriceLearning.LowerBound.maxima_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:25:53.266468+00:00
-- url     : https://prove2.me/submissions/6a9d15aa-1cc9-44bb-9f51-cf9f552bdbc6

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

set_option autoImplicit false
open MeasureTheory FirstPriceLearning.LowerBound

lemma cdf_two (p b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FirstPriceLearning.Stochastic.cdf (twoPointLaw p) b =
      (if 1 / 3 ≤ b then p else 0) + (if 2 / 3 ≤ b then 1 - p else 0) := by
  unfold FirstPriceLearning.Stochastic.cdf twoPointLaw
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  simp only [Set.indicator, Set.mem_Iic, Pi.one_apply, ENNReal.smul_def, smul_eq_mul]
  by_cases h1 : 1 / 3 ≤ b <;> by_cases h2 : 2 / 3 ≤ b <;> simp only [h1, h2, if_true, if_false, mul_one, mul_zero, add_zero, zero_add, ENNReal.toReal_add, ENNReal.coe_toReal, Real.coe_toNNReal _ hp0, Real.coe_toNNReal _ (sub_nonneg.mpr hp1), ENNReal.coe_ne_top, ne_eq, not_false_eq_true, ENNReal.toReal_zero]

lemma expR (p b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FirstPriceLearning.Stochastic.expReward (twoPointLaw p) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then p else 0) + (if 2 / 3 ≤ b then 1 - p else 0)) := by
  unfold FirstPriceLearning.Stochastic.expReward
  rw [cdf_two p b hp0 hp1]

lemma maxima_aux (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) ((1 + 2 * Δ) / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) (1 / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1)
      (2 / 3) := by
  have hE1 : ∀ b, FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then 1 / 2 + Δ else 0) + (if 2 / 3 ≤ b then 1 - (1 / 2 + Δ) else 0)) :=
    fun b => expR _ b (by linarith) (by linarith)
  have hE2 : ∀ b, FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b =
      (1 - b) * ((if 1 / 3 ≤ b then 1 / 2 - Δ else 0) + (if 2 / 3 ≤ b then 1 - (1 / 2 - Δ) else 0)) :=
    fun b => expR _ b (by linarith) (by linarith)
  refine ⟨⟨⟨1 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩, ⟨⟨2 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩,
    ⟨⟨1 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩⟩
  · simp only [hE1]; norm_num; ring
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE1]
    split_ifs <;> nlinarith
  · simp only [hE2]; norm_num
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE2]
    split_ifs <;> nlinarith
  · simp only [hE1, hE2]; norm_num; ring
  · rintro _ ⟨b, ⟨hb0, hb1⟩, rfl⟩
    simp only [hE1, hE2]
    split_ifs <;> nlinarith

theorem solution (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) ((1 + 2 * Δ) / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1) (1 / 3) ∧
    IsGreatest ((fun b => FirstPriceLearning.Stochastic.expReward (lawG1 Δ) 1 b + FirstPriceLearning.Stochastic.expReward (lawG2 Δ) 1 b) '' Set.Icc (0 : ℝ) 1)
      (2 / 3) := maxima_aux Δ hΔ0 hΔ1
