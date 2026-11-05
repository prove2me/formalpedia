-- Prove2me | solution 1 for ExploreFirst.Relative.equation_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:07:23.631564+00:00
-- url     : https://prove2.me/submissions/e0cde274-79d6-4072-9879-07f288ee9bfa

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting
import Theorems.Thm_ExploreFirst_Relative_symmetry_half
import Theorems.Thm_ExploreFirst_FundIneq_lemma_1
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace EFRelEq12Aux

lemma armPullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  simp [armPullCount, Finset.sum_boole]

lemma armPullCount_le {K n : ℕ} (i : Fin K) (h : BanditHistory K n) : armPullCount i h ≤ n := by
  rw [armPullCount_eq_sum]
  calc (∑ t : Fin n, if (h t).1 = i then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> simp)
    _ = n := by simp

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

lemma integrable_of_bdd {K n : ℕ} (μ : Measure (BanditHistory K n)) [IsFiniteMeasure μ]
    (f : BanditHistory K n → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ h, |f h| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun h => by rw [Real.norm_eq_abs]; exact hb h))

lemma measurable_pullsPlus {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => ExploreFirst.Relative.pullsPlus i h) :=
  (measurable_armPullCount_real i).max measurable_const

lemma one_le_pullsPlus {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    1 ≤ ExploreFirst.Relative.pullsPlus i h := le_max_right _ _

/-- The test function `Z = N⁺_a / (N⁺_a + N⁺_{a'})`. -/
noncomputable def Zf {K n : ℕ} (a a' : Fin K) (h : BanditHistory K n) : ℝ :=
  ExploreFirst.Relative.pullsPlus a h /
    (ExploreFirst.Relative.pullsPlus a h + ExploreFirst.Relative.pullsPlus a' h)

lemma Zf_mem {K n : ℕ} (a a' : Fin K) (h : BanditHistory K n) : Zf a a' h ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := one_le_pullsPlus a h
  have h2 := one_le_pullsPlus a' h
  unfold Zf
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

lemma measurable_Zf {K n : ℕ} (a a' : Fin K) : Measurable (Zf a a' : BanditHistory K n → ℝ) :=
  (measurable_pullsPlus a).div ((measurable_pullsPlus a).add (measurable_pullsPlus a'))

instance bernoulliLaw_isFinite (p : ℝ) : IsFiniteMeasure (ExploreFirst.FundIneq.bernoulliLaw p) := by
  constructor
  simp only [ExploreFirst.FundIneq.bernoulliLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

lemma klBer_self (p : ℝ) : ExploreFirst.FundIneq.klBer p p = 0 := by
  unfold ExploreFirst.FundIneq.klBer
  exact InformationTheory.klDiv_self _

lemma klBer_zero_right (p : ℝ) (hp : 0 < p) : ExploreFirst.FundIneq.klBer p 0 = ⊤ := by
  unfold ExploreFirst.FundIneq.klBer
  apply InformationTheory.klDiv_of_not_ac
  intro hac
  have h0 : ExploreFirst.FundIneq.bernoulliLaw 0 {1} = 0 := by
    simp [ExploreFirst.FundIneq.bernoulliLaw]
  have h1 := hac h0
  simp [ExploreFirst.FundIneq.bernoulliLaw] at h1
  linarith

lemma klDiv_mix_ne_top (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv P ((2 : ℝ≥0∞)⁻¹ • (P + Q)) ≠ ⊤ := by
  set m := (2 : ℝ≥0∞)⁻¹ • (P + Q) with hm
  have hle : (2 : ℝ≥0∞)⁻¹ • P ≤ m := by
    rw [hm, smul_add]; exact Measure.le_add_right le_rfl
  haveI : IsFiniteMeasure m := by
    constructor
    rw [hm, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hac : P ≪ m := by
    have : P ≤ (2 : ℝ≥0∞) • m := by
      rw [hm, smul_smul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]
      exact Measure.le_add_right le_rfl
    exact Measure.absolutelyContinuous_of_le_smul this
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hac]
  have h1 := Measure.rnDeriv_le_one_of_le hle
  have h2 := Measure.rnDeriv_smul_left_of_ne_top' P m (r := (2 : ℝ≥0∞)⁻¹) (by simp)
  have hb : ∀ᵐ x ∂m, ENNReal.ofReal (InformationTheory.klFun (P.rnDeriv m x).toReal) ≤ 1 := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2] at hx1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hx1
    have hx3 : P.rnDeriv m x ≤ 2 := by
      calc P.rnDeriv m x = 2 * ((2 : ℝ≥0∞)⁻¹ * P.rnDeriv m x) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * 1 := by gcongr
        _ = 2 := mul_one 2
    have hy0 : 0 ≤ (P.rnDeriv m x).toReal := ENNReal.toReal_nonneg
    have hy2 : (P.rnDeriv m x).toReal ≤ 2 := by
      have := ENNReal.toReal_mono (by norm_num) hx3
      simpa using this
    rw [ENNReal.ofReal_le_one, InformationTheory.klFun_apply]
    set y := (P.rnDeriv m x).toReal
    rcases hy0.eq_or_lt with h | h
    · rw [← h]; simp
    · have hl : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos h
      nlinarith [mul_le_mul_of_nonneg_left hl h.le, mul_nonneg h.le (by linarith : (0 : ℝ) ≤ 2 - y)]
  refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂m) ?_ (lintegral_mono_ae hb)
  simp [measure_ne_top]

lemma expPulls_nonneg {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (a : Fin K) :
    0 ≤ ExploreFirst.FundIneq.expPulls ν π T a :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

lemma integrable_pulls {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (a : Fin K) :
    Integrable (fun h : BanditHistory K T => (armPullCount a h : ℝ)) (banditMeasure ν π T) :=
  integrable_of_bdd _ _ (measurable_armPullCount_real a) T (fun h => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast armPullCount_le a h)

/-- If arm `a` is almost surely never pulled under `ν`, then changing the law of arm `a`
does not change the law of the history. -/
lemma banditMeasure_eq_of_expPulls_zero {K : ℕ} (ν ν' : StochasticBandit K) (π : BanditPolicy K)
    (T : ℕ) (a : Fin K) (hne : ∀ k, k ≠ a → ν'.P k = ν.P k)
    (h0 : ExploreFirst.FundIneq.expPulls ν π T a = 0) :
    banditMeasure ν π T = banditMeasure ν' π T := by
  classical
  let m : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (ν.P a + ν'.P a)
  have hmprob : IsProbabilityMeasure m := by
    constructor
    simp only [m, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  let ν'' : StochasticBandit K :=
    ⟨fun k => if k = a then m else ν.P k, fun k => by
      by_cases hk : k = a
      · simp only [hk, if_true]; exact hmprob
      · simp only [hk, if_false]; infer_instance⟩
  have hP'' : ∀ k, ν''.P k = if k = a then m else ν.P k := fun k => rfl
  have hKL1 : ∀ i, InformationTheory.klDiv (ν.P i) (ν''.P i) ≠ ⊤ := by
    intro i
    rw [hP'']
    by_cases hi : i = a
    · subst hi; rw [if_pos rfl]; exact klDiv_mix_ne_top _ _
    · rw [if_neg hi, InformationTheory.klDiv_self]; exact ENNReal.zero_ne_top
  have hKL2 : ∀ i, InformationTheory.klDiv (ν'.P i) (ν''.P i) ≠ ⊤ := by
    intro i
    rw [hP'']
    by_cases hi : i = a
    · subst hi; rw [if_pos rfl]
      have := klDiv_mix_ne_top (ν'.P i) (ν.P i)
      rwa [add_comm] at this
    · rw [if_neg hi, ← hne i hi, InformationTheory.klDiv_self]; exact ENNReal.zero_ne_top
  -- Step 1: the laws under `ν` and `ν''` agree.
  have heq1 : banditMeasure ν π T = banditMeasure ν'' π T := by
    rw [← InformationTheory.klDiv_eq_zero_iff,
      BanditAlgorithm.bandit_divergence_decomposition ν ν'' hKL1 π T]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hi : i = a
    · subst hi
      have : ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π T = 0 := h0
      rw [this]; simp
    · rw [hP'', if_neg hi, InformationTheory.klDiv_self, mul_zero]
  -- Step 2: the indicator-like test function `Z₁ = min(N_a, 1)`.
  let Z1 : BanditHistory K T → ℝ := fun h => min (armPullCount a h : ℝ) 1
  have hZ1m : Measurable Z1 := (measurable_armPullCount_real a).min measurable_const
  have hZ1mem : ∀ h, Z1 h ∈ Set.Icc (0 : ℝ) 1 :=
    fun h => ⟨le_min (Nat.cast_nonneg _) zero_le_one, min_le_right _ _⟩
  have hZ1int : ∀ μ : StochasticBandit K, Integrable Z1 (banditMeasure μ π T) := fun μ =>
    integrable_of_bdd _ _ hZ1m 1 (fun h => by
      rw [abs_of_nonneg (hZ1mem h).1]; exact (hZ1mem h).2)
  have hEnu : ∫ h, Z1 h ∂banditMeasure ν π T = 0 := by
    apply le_antisymm
    · calc ∫ h, Z1 h ∂banditMeasure ν π T
          ≤ ∫ h, (armPullCount a h : ℝ) ∂banditMeasure ν π T :=
            integral_mono (hZ1int ν) (integrable_pulls ν π T a) (fun h => min_le_left _ _)
        _ = 0 := h0
    · exact integral_nonneg (fun h => (hZ1mem h).1)
  have hEnu'' : ∫ h, Z1 h ∂banditMeasure ν'' π T = 0 := by rw [← heq1]; exact hEnu
  -- Step 3: under `ν'`, `Z₁` has mean zero.
  have hfin2 : InformationTheory.klDiv (banditMeasure ν' π T) (banditMeasure ν'' π T) ≠ ⊤ := by
    rw [BanditAlgorithm.bandit_divergence_decomposition ν' ν'' hKL2 π T]
    exact ENNReal.sum_ne_top.2 (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKL2 i))
  have key := ExploreFirst.FundIneq.lemma_1 (banditMeasure ν' π T) (banditMeasure ν'' π T)
    Z1 hZ1m hZ1mem
  rw [hEnu''] at key
  have hp0 : ∫ h, Z1 h ∂banditMeasure ν' π T = 0 := by
    apply le_antisymm _ (integral_nonneg (fun h => (hZ1mem h).1))
    by_contra hpos
    rw [not_le] at hpos
    rw [klBer_zero_right _ hpos] at key
    exact hfin2 (top_le_iff.1 key)
  -- Step 4: hence arm `a` is never pulled under `ν'` either.
  have h0' : ∫ h, (armPullCount a h : ℝ) ∂banditMeasure ν' π T = 0 := by
    apply le_antisymm _ (integral_nonneg (fun _ => Nat.cast_nonneg _))
    calc ∫ h, (armPullCount a h : ℝ) ∂banditMeasure ν' π T
        ≤ ∫ h, (T : ℝ) * Z1 h ∂banditMeasure ν' π T := by
          refine integral_mono (integrable_pulls ν' π T a) ((hZ1int ν').const_mul _) (fun h => ?_)
          show (armPullCount a h : ℝ) ≤ (T : ℝ) * min (armPullCount a h : ℝ) 1
          rcases Nat.eq_zero_or_pos (armPullCount a h) with hz | hz
          · rw [hz]; simp
          · have h1 : (1 : ℝ) ≤ armPullCount a h := by exact_mod_cast hz
            rw [min_eq_right h1, mul_one]
            exact_mod_cast armPullCount_le a h
      _ = 0 := by rw [integral_const_mul, hp0, mul_zero]
  -- Step 5: the laws under `ν'` and `ν''` agree.
  have heq2 : banditMeasure ν' π T = banditMeasure ν'' π T := by
    rw [← InformationTheory.klDiv_eq_zero_iff,
      BanditAlgorithm.bandit_divergence_decomposition ν' ν'' hKL2 π T]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hi : i = a
    · subst hi
      rw [h0']; simp
    · rw [hP'', if_neg hi, ← hne i hi, InformationTheory.klDiv_self, mul_zero]
  exact heq1.trans heq2.symm

end EFRelEq12Aux

open EFRelEq12Aux in
open ExploreFirst.Relative in
theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (T : ℕ) (hT : 1 ≤ T) :
    ExploreFirst.FundIneq.klBer (∫ h, ExploreFirst.Relative.pullsPlus a h / (ExploreFirst.Relative.pullsPlus a h + ExploreFirst.Relative.pullsPlus a' h) ∂(banditMeasure ν π T)) (1 / 2) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) * InformationTheory.klDiv (ν.P a) (ν'.P a) := by
  classical
  have hsym := ExploreFirst.Relative.symmetry_half 𝒟 h𝒟 π hπ ν hν a a' ha ha' ν' hν'_ne hν'_a T hT
  have hhalf : ∫ h, Zf a a' h ∂(banditMeasure ν' π T) = 1 / 2 := hsym.1.trans hsym.2
  have hZ : ∀ μ : Measure (BanditHistory K T),
      ∫ h, ExploreFirst.Relative.pullsPlus a h /
        (ExploreFirst.Relative.pullsPlus a h + ExploreFirst.Relative.pullsPlus a' h) ∂μ =
      ∫ h, Zf a a' h ∂μ := fun μ => rfl
  rw [hZ]
  by_cases hfin : InformationTheory.klDiv (ν.P a) (ν'.P a) = ⊤
  · rw [hfin]
    by_cases hpos : 0 < ExploreFirst.FundIneq.expPulls ν π T a
    · rw [ENNReal.mul_top (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hpos)]
      exact le_top
    · have h0 : ExploreFirst.FundIneq.expPulls ν π T a = 0 :=
        le_antisymm (not_lt.1 hpos) (expPulls_nonneg ν π T a)
      have heq := banditMeasure_eq_of_expPulls_zero ν ν' π T a hν'_ne h0
      rw [heq, hhalf, klBer_self]
      exact zero_le
  · have hKLall : ∀ i, InformationTheory.klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
      intro i
      by_cases hi : i = a
      · subst hi; exact hfin
      · rw [hν'_ne i hi, InformationTheory.klDiv_self]; exact ENNReal.zero_ne_top
    have key := ExploreFirst.FundIneq.lemma_1 (banditMeasure ν π T) (banditMeasure ν' π T)
      (Zf a a') (measurable_Zf a a') (Zf_mem a a')
    rw [hhalf] at key
    refine key.trans (le_of_eq ?_)
    rw [BanditAlgorithm.bandit_divergence_decomposition ν ν' hKLall π T,
      Finset.sum_eq_single a]
    · rfl
    · intro i _ hi
      rw [hν'_ne i hi, InformationTheory.klDiv_self, mul_zero]
    · simp
