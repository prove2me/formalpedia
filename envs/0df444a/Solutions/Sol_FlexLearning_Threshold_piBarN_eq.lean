-- Prove2me | solution 1 for FlexLearning.Threshold.piBarN_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:36:22.505131+00:00
-- url     : https://prove2.me/submissions/a2e4e16a-9d13-4d8d-8dd2-627d17db1e95

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model
import Theorems.Thm_FlexLearning_Threshold_lemma_3

open FlexLearning.Threshold MeasureTheory

namespace FlexLAuxN

lemma prior_prob (x U : ℝ) (hU : 0 < U) : IsProbabilityMeasure (prior x U) := by
  constructor
  unfold prior
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul]
  have : ENNReal.ofReal (x + U - x) = ENNReal.ofReal U := by congr 1; ring
  rw [this, ENNReal.inv_mul_cancel (by simp [hU]) ENNReal.ofReal_ne_top]

lemma prior_integrable (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (prior x U) := by
  unfold prior
  exact (hf.continuousOn.integrableOn_Icc).smul_measure (by simp [hU])

lemma piN_split (p c x U : ℝ) (hU : 0 < U) (Q : ℝ × ℝ) :
    piN p c x U Q = nvProfit p c (prior x U) Q.1 + nvProfit p c (prior x U) Q.2 := by
  haveI := prior_prob x U hU
  have h1 := prior_integrable x U hU (fun d => p * min d Q.1)
    (continuous_const.mul (continuous_id.min continuous_const))
  have h2 := prior_integrable x U hU (fun d => p * min d Q.2)
    (continuous_const.mul (continuous_id.min continuous_const))
  unfold piN nvProfit prior2
  rw [integral_add (h1.comp_fst _) (h2.comp_snd _), integral_fun_fst (fun d => p * min d Q.1),
    integral_fun_snd (fun d => p * min d Q.2), integral_sub h1 (integrable_const _),
    integral_sub h2 (integrable_const _)]
  simp; ring

end FlexLAuxN

open FlexLAuxN in
theorem solution (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    piBarN p c x U = 2 * (p - c) * x + U * ((p - c) ^ 2 / p) := by
  obtain ⟨h0, hval, hmax⟩ := FlexLearning.Threshold.lemma_3 p c x U hc hcp hx hU
  set Qb := x + U * ((p - c) / p)
  unfold piBarN
  apply IsGreatest.csSup_eq
  refine ⟨⟨(Qb, Qb), ⟨h0, h0⟩, ?_⟩, ?_⟩
  · rw [piN_split p c x U hU, hval]; ring
  · rintro _ ⟨Q, ⟨hQ1, hQ2⟩, rfl⟩
    rw [piN_split p c x U hU]
    have := hmax _ hQ1
    have := hmax _ hQ2
    rw [hval] at *
    linarith
