-- Prove2me | solution 1 for ExploreFirst.Collective.equation_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:33:44.78227+00:00
-- url     : https://prove2.me/submissions/b0fb716c-f542-476f-9b21-f9ab8786c43d

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting
import Theorems.Thm_ExploreFirst_Collective_kl_display
import Theorems.Thm_ExploreFirst_Collective_lemma_6
import Theorems.Thm_ExploreFirst_Collective_lemma_2

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace EFCEq14Aux

lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  simp [armPullCount, Finset.sum_boole]

lemma sum_armPullCount {K n : ℕ} (h : BanditHistory K n) :
    ∑ i : Fin K, armPullCount i h = n := by
  simp_rw [armPullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

lemma measurable_armPullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount i h) := by
  have : (fun h : BanditHistory K n => armPullCount i h) =
      fun h => ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
    funext h; exact armPullCount_eq_sum i h
  rw [this]
  refine Finset.measurable_sum _ (fun t _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton i)

lemma measurable_armPullCount_real {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => (armPullCount i h : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (measurable_armPullCount i)

lemma integrable_armPullCount {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (n : ℕ)
    (i : Fin K) :
    Integrable (fun h : BanditHistory K n => (armPullCount i h : ℝ)) (banditMeasure ν π n) := by
  refine Integrable.of_bound (measurable_armPullCount_real i).aestronglyMeasurable (n : ℝ) ?_
  refine Filter.Eventually.of_forall (fun h => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : armPullCount i h ≤ n := by
    calc armPullCount i h ≤ ∑ j : Fin K, armPullCount j h :=
          Finset.single_le_sum (f := fun j => armPullCount j h) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
      _ = n := sum_armPullCount h
  exact_mod_cast this

lemma sum_expPulls {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (n : ℕ) :
    ∑ i : Fin K, ExploreFirst.FundIneq.expPulls ν π n i = n := by
  unfold ExploreFirst.FundIneq.expPulls
  rw [← integral_finsetSum _ (fun i _ => integrable_armPullCount ν π n i)]
  have : (fun h : BanditHistory K n => ∑ i : Fin K, (armPullCount i h : ℝ)) = fun _ => (n : ℝ) := by
    funext h; exact_mod_cast sum_armPullCount h
  rw [this]
  simp

end EFCEq14Aux

open EFCEq14Aux in
theorem solution {K : ℕ}
    (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K)
    (w : Fin K) (hw : w ∈ ExploreFirst.Collective.worstArms ν)
    (hwmin : (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) = ExploreFirst.Collective.kMax ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (νt : StochasticBandit K) (hνt : ∀ a, νt.P a = ν.P w)
    (T : ℕ) (hT : 1 ≤ T)
    (hfin : ExploreFirst.Collective.kMax ν ≠ ⊤) :
    (∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls νdd π T a) / T
      ≤ ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K *
          (1 + 2 * T * (ExploreFirst.Collective.kMax ν).toReal + Real.sqrt (2 * T * (ExploreFirst.Collective.kMax ν).toReal)) := by
  set S := ExploreFirst.Asymptotic.optimalArms ν with hS
  set k := (ExploreFirst.Collective.kMax ν).toReal with hk
  set p : ℝ := (S.card : ℝ) / K with hp
  set x : ℝ := (∑ a ∈ S, ExploreFirst.FundIneq.expPulls νdd π T a) / T with hx
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hp0 : 0 ≤ p := by positivity
  have hsq0 : 0 ≤ Real.sqrt (2 * T * k) := Real.sqrt_nonneg _
  have hT0 : (0 : ℝ) ≤ 2 * T * k := by positivity
  by_cases hxp : x ≤ p
  · calc x ≤ p := hxp
      _ = p * 1 := (mul_one p).symm
      _ ≤ p * (1 + 2 * T * k + Real.sqrt (2 * T * k)) := by
          apply mul_le_mul_of_nonneg_left _ hp0; linarith
  push_neg at hxp
  -- x ≤ 1
  have hx1 : x ≤ 1 := by
    have hnn : ∀ a, 0 ≤ ExploreFirst.FundIneq.expPulls νdd π T a := fun a =>
      integral_nonneg (fun h => Nat.cast_nonneg _)
    have hle : (∑ a ∈ S, ExploreFirst.FundIneq.expPulls νdd π T a) ≤ T := by
      calc (∑ a ∈ S, ExploreFirst.FundIneq.expPulls νdd π T a)
          ≤ ∑ a : Fin K, ExploreFirst.FundIneq.expPulls νdd π T a :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hnn a)
        _ = T := sum_expPulls νdd π T
    rw [hx, div_le_one hTpos]; exact hle
  have hxpos : 0 < x := lt_of_le_of_lt hp0 hxp
  have hkl := ExploreFirst.Collective.kl_display 𝒟 h𝒟 π hπ ν hν hK w hw hwmin νdd hνdd νt hνt T hT
  have h6 := ExploreFirst.Collective.lemma_6 p x hp0 hxp hx1
  have hrhs : ENNReal.ofReal ((T : ℝ) * S.card / K) * ExploreFirst.Collective.kMax ν =
      ENNReal.ofReal (T * p * k) := by
    rw [hk, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin, hp, mul_div_assoc]
  rw [hrhs] at hkl
  have hineq : (p - x) ^ 2 / (2 * x) ≤ T * p * k := by
    have h1 : ENNReal.ofReal ((p - x) ^ 2 / (2 * x)) ≤ ENNReal.ofReal (T * p * k) :=
      (ENNReal.ofReal_le_ofReal h6.2).trans (h6.1.trans hkl)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hquad : (x - p) ^ 2 ≤ (2 * T * p * k) * x := by
    rw [div_le_iff₀ (by positivity)] at hineq
    nlinarith [hineq]
  have h2 := ExploreFirst.Collective.lemma_2 x p (2 * T * p * k) hp0 (by positivity) hquad
  have hsqrt : Real.sqrt (p * (2 * T * p * k)) = p * Real.sqrt (2 * T * k) := by
    rw [show p * (2 * T * p * k) = p ^ 2 * (2 * T * k) by ring, Real.sqrt_mul (sq_nonneg p),
      Real.sqrt_sq hp0]
  rw [hsqrt] at h2
  calc x ≤ p + 2 * T * p * k + p * Real.sqrt (2 * T * k) := h2
    _ = p * (1 + 2 * T * k + Real.sqrt (2 * T * k)) := by ring
