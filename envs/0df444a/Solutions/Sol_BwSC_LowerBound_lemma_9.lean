-- Prove2me | solution 1 for BwSC.LowerBound.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:12:39.687807+00:00
-- url     : https://prove2.me/submissions/acf0f518-c41f-41aa-848c-8af67041feab

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_BwSC_LowerBound_lemma_8
import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.RegAux

lemma armPullCount_eq {K T : ℕ} (i : Fin K) (h : BanditHistory K T) :
    (armPullCount i h : ℝ) = ∑ t : Fin T, if (h t).1 = i then (1 : ℝ) else 0 := by
  classical
  simp only [armPullCount, Finset.sum_boole]
  congr 1
  congr 1
  ext t; simp

lemma regretOf_eq {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) :
    regretOf μ h = ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
  classical
  simp_rw [armPullCount_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold regretOf
  rw [Finset.sum_sub_distrib]
  simp

lemma measurable_armPullCount {K T : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) := by
  have : (fun h : BanditHistory K T => (armPullCount i h : ℝ)) =
      (fun a : Fin T → Fin K => (({t | a t = i}.toFinset.card : ℕ) : ℝ)) ∘ actions := by
    funext h; rfl
  rw [this]
  exact (measurable_of_finite _).comp measurable_actions

lemma integrable_armPullCount {K T : ℕ} (i : Fin K) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (fun h => (armPullCount i h : ℝ)) P := by
  refine Integrable.of_bound (C := T) (measurable_armPullCount i).aestronglyMeasurable
    (ae_of_all _ (fun h => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : armPullCount i h ≤ T := by
    unfold armPullCount
    exact (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast this

lemma integrable_regretOf {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (regretOf μ) P := by
  have : (regretOf μ : BanditHistory K T → ℝ) =
      fun h => ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
    funext h; exact regretOf_eq μ h
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (integrable_armPullCount i P).const_mul _)

lemma regretOf_nonneg {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) : 0 ≤ regretOf μ h := by
  rw [regretOf_eq]
  refine Finset.sum_nonneg (fun i _ => mul_nonneg ?_ (Nat.cast_nonneg _))
  exact sub_nonneg.mpr (le_ciSup (Set.finite_range μ).bddAbove i)

lemma gap_gaussian {K : ℕ} (μ : Fin K → ℝ) (i : Fin K) :
    banditGap (gaussianBandit μ) i = (⨆ j, μ j) - μ i := by
  simp [banditGap, banditOptimalMean, banditArmMean, gaussianBandit, integral_id_gaussianReal]

lemma regret_eq_integral {K T : ℕ} (μ : Fin K → ℝ) (π : BanditPolicy K) :
    banditRegret (gaussianBandit μ) π T =
      ∫ h, regretOf μ h ∂(banditMeasure (gaussianBandit μ) π T) := by
  rw [bandit_regret_decomposition _ (fun i => (memLp_id_gaussianReal 1).integrable le_rfl) π T]
  simp_rw [regretOf_eq]
  rw [integral_finsetSum _ (fun i _ => (integrable_armPullCount i _).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, gap_gaussian]

lemma regret_ge_setIntegral {K T : ℕ} (μ : Fin K → ℝ) (π : BanditPolicy K)
    (E : Set (BanditHistory K T)) :
    ∫ h in E, regretOf μ h ∂(banditMeasure (gaussianBandit μ) π T) ≤
      banditRegret (gaussianBandit μ) π T := by
  rw [regret_eq_integral]
  exact setIntegral_le_integral (integrable_regretOf μ _) (ae_of_all _ (regretOf_nonneg μ))

/-- `m^(1-e) T^e ≥ m` for `e ≥ 0`, `1 ≤ m ≤ T`. -/
lemma grid_ge (m T e : ℝ) (hm : 0 < m) (hmT : m ≤ T) (he : 0 ≤ e) :
    m ≤ m ^ (1 - e) * T ^ e := by
  have hT : 0 < T := lt_of_lt_of_le hm hmT
  have e1 : m ^ (1 - e) * T ^ e = m * (T / m) ^ e := by
    rw [Real.div_rpow hT.le hm.le, Real.rpow_sub hm, Real.rpow_one]
    have : 0 < m ^ e := by positivity
    field_simp
  rw [e1]
  have : 1 ≤ (T / m) ^ e := Real.one_le_rpow (by rw [le_div_iff₀ hm]; linarith) he
  nlinarith

/-- `√(m / t) ≤ 2` when `t = ⌊x⌋₊` with `x ≥ m ≥ 2`. -/
lemma sqrt_ratio_le (m x : ℝ) (hm : 2 ≤ m) (hx : m ≤ x) :
    Real.sqrt (m / (⌊x⌋₊ : ℝ)) ≤ 2 := by
  have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have ht : m / 2 ≤ (⌊x⌋₊ : ℝ) := by linarith
  have htpos : 0 < (⌊x⌋₊ : ℝ) := by linarith
  rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ htpos]; linarith

lemma aExp_pos (q : ℕ) : 0 < aExp q := by
  have : (2 : ℝ) ^ (-(q : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
  unfold aExp
  apply div_pos one_pos; linarith

lemma two_sub_pow_nonneg (i : ℕ) (hi : 1 ≤ i) : 0 ≤ 2 - (2 : ℝ) ^ (1 - (i : ℝ)) := by
  have : (2 : ℝ) ^ (1 - (i : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  linarith

lemma rIdx_le {S K : ℕ} (hK : 1 < K) : rIdx S K ≤ (K : ℤ) - 2 := by
  unfold rIdx qIdx
  by_cases hS : S = 0
  · subst hS; simp; omega
  · rw [if_neg hS]
    have hdm := Nat.div_add_mod (S - 1) (K - 1)
    have hlt := Nat.mod_lt (S - 1) (by omega : K - 1 > 0)
    have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
    have e : (S : ℤ) - 1 - (((S - 1) / (K - 1) : ℕ) : ℤ) * ((K : ℤ) - 1) =
        (((S - 1) % (K - 1) : ℕ) : ℤ) := by
      rw [← hS1, ← hK1]; push_cast; zify at hdm; linarith
    rw [e]
    zify at hlt; push_cast at hlt ⊢; omega

lemma rIdx_ge (S K : ℕ) : (-1 : ℤ) ≤ rIdx S K := by
  unfold rIdx qIdx
  by_cases hS : S = 0
  · subst hS; simp
  · rw [if_neg hS]
    have hdm := Nat.div_add_mod (S - 1) (K - 1)
    have : ((S - 1) / (K - 1)) * (K - 1) ≤ S - 1 := Nat.div_mul_le_self _ _
    have hS1 : ((S - 1 : ℕ) : ℤ) = (S : ℤ) - 1 := by omega
    by_cases hK : K = 0
    · subst hK; simp; omega
    · have hK1 : ((K - 1 : ℕ) : ℤ) = (K : ℤ) - 1 := by omega
      rw [← hK1]
      have h2 : ((((S - 1) / (K - 1)) * (K - 1) : ℕ) : ℤ) ≤ ((S - 1 : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at h2
      omega

/-- `t^{(1)}_i ≥ (K - r)/2` for `i ≥ 1`, in the form `√((K-r)/t^{(1)}_i) ≤ 2`. -/
lemma sqrt_t1 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (i : ℕ) (hi : 1 ≤ i) :
    Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) ≤ 2 := by
  have hr1 : (rIdx S K : ℝ) ≤ (K : ℝ) - 2 := by exact_mod_cast rIdx_le (S := S) hK
  have hr2 : (-1 : ℝ) ≤ (rIdx S K : ℝ) := by exact_mod_cast rIdx_ge S K
  have hTK : (2 * K : ℝ) ≤ T := by exact_mod_cast hT
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  unfold t1
  rw [if_neg (by omega)]
  apply sqrt_ratio_le _ _ (by linarith)
  apply grid_ge _ _ _ (by linarith) (by linarith)
  exact mul_nonneg (two_sub_pow_nonneg i hi) (aExp_pos _).le

lemma abs_Δ1_le {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (hq : 1 ≤ qIdx S K) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) : |Δ1 S K T j| ≤ 1 := by
  have hn : (2 : ℝ) ≤ (qIdx S K : ℝ) + 2 := by have : (0:ℝ) ≤ qIdx S K := by positivity
                                               linarith
  have key : ∀ i, 1 ≤ i → (1 / (2 * ((qIdx S K : ℝ) + 2))) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) ≤ 1 := by
    intro i hi
    have h := sqrt_t1 (S := S) hK hT i hi
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hs0 : ∀ i, 0 ≤ (1 / (2 * ((qIdx S K : ℝ) + 2))) *
      Real.sqrt (((K : ℝ) - (rIdx S K : ℝ)) / (t1 S K T i : ℝ)) := fun i => by positivity
  simp only [Finset.mem_Icc] at hj
  unfold Δ1
  split_ifs with h1 h2
  · simp
  · rw [abs_neg, abs_of_nonneg (hs0 _)]; exact key _ hq
  · rw [abs_of_nonneg (hs0 _)]; exact key _ (by omega)

lemma spread_update {K : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : |Δ| ≤ 1) (i i' : Fin K) :
    |Function.update (0 : Fin K → ℝ) k Δ i - Function.update (0 : Fin K → ℝ) k Δ i'| ≤ 1 := by
  by_cases hi : i = k <;> by_cases hi' : i' = k
  · subst hi; subst hi'; simp
  · subst hi; simp [Function.update_of_ne hi', hΔ]
  · subst hi'; simp [Function.update_of_ne hi, abs_neg, hΔ]
  · simp [Function.update_of_ne hi, Function.update_of_ne hi']

end BwSC.LowerBound.RegAux

open BwSC.LowerBound BwSC.LowerBound.RegAux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) (hq : 1 ≤ qIdx S K)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      Rbad S K T *
          ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal ≤
        banditRegret (gaussianBandit (envAlt1 S K T j k)) π T) ∧
    (∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K, ∀ i i' : Fin K,
      |envAlt1 S K T j k i - envAlt1 S K T j k i'| ≤ 1) ∧
    Rbad S K T * pbar1 π S T ≤
      1 / (((qIdx S K : ℝ) + 2) * K) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          banditRegret (gaussianBandit (envAlt1 S K T j k)) π T := by
  have H1 : ∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      Rbad S K T *
          ((banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k)).toReal ≤
        banditRegret (gaussianBandit (envAlt1 S K T j k)) π T := fun j hj k =>
    (lemma_8 hK hT π hπ hq hstand j hj k).trans (regret_ge_setIntegral _ π _)
  refine ⟨H1, fun j hj k i i' => spread_update k _ (abs_Δ1_le hK hT hq j hj) i i', ?_⟩
  unfold pbar1
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => H1 j hj k)
