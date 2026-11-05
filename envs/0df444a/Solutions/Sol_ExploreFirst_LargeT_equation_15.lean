-- Prove2me | solution 1 for ExploreFirst.LargeT.equation_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:01:35.374234+00:00
-- url     : https://prove2.me/submissions/401f5d53-3df9-4337-980e-fed96e1c6caa

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_ExploreFirst_FundIneq_lemma_1
import Theorems.Thm_ExploreFirst_Asymptotic_kl_ge_of_eq_11

open MeasureTheory BanditAlgorithm

namespace EFCoreCOM

theorem pullCount_eq_sum {K n : ℕ} (i : Fin K) (h : BanditHistory K n) :
    armPullCount i h = ∑ t : Fin n, if (h t).1 = i then 1 else 0 := by
  unfold armPullCount
  rw [Finset.sum_boole]
  simp [Set.toFinset_setOf]

theorem measurable_pullCount {K n : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K n => (armPullCount i h : ℝ)) := by
  have : (fun h : BanditHistory K n => (armPullCount i h : ℝ)) =
      fun h => ∑ t : Fin n, (if (h t).1 = i then (1 : ℝ) else 0) := by
    funext h
    rw [pullCount_eq_sum]
    push_cast
    rfl
  rw [this]
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite _ measurable_const measurable_const
  have hm : Measurable (fun h : BanditHistory K n => (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact hm (measurableSet_singleton i)

theorem sum_pullCount_le {K n : ℕ} (S : Finset (Fin K)) (h : BanditHistory K n) :
    ∑ b ∈ S, armPullCount b h ≤ n := by
  simp_rw [pullCount_eq_sum]
  rw [Finset.sum_comm]
  calc ∑ t : Fin n, ∑ b ∈ S, (if (h t).1 = b then 1 else 0)
      ≤ ∑ _t : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro t _
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp
    _ = n := by simp

theorem sum_pullCount_univ {K n : ℕ} (h : BanditHistory K n) :
    ∑ b, armPullCount b h = n := by
  simp_rw [pullCount_eq_sum]
  rw [Finset.sum_comm]
  simp

theorem integrable_pullCount {K n : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K)
    (i : Fin K) :
    Integrable (fun h : BanditHistory K n => (armPullCount i h : ℝ)) (banditMeasure ν π n) := by
  apply Integrable.of_bound (C := (n : ℝ)) (measurable_pullCount i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := sum_pullCount_le {i} h
  simp at this
  exact_mod_cast this

theorem expPulls_nonneg {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (i : Fin K) : 0 ≤ ExploreFirst.FundIneq.expPulls ν π T i := by
  unfold ExploreFirst.FundIneq.expPulls
  exact integral_nonneg (fun _ => by positivity)

theorem sum_expPulls_univ {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) :
    ∑ b, ExploreFirst.FundIneq.expPulls ν π T b = T := by
  unfold ExploreFirst.FundIneq.expPulls
  rw [← integral_finsetSum _ (fun i _ => integrable_pullCount ν π i)]
  have : (fun h : BanditHistory K T => ∑ i, (armPullCount i h : ℝ)) = fun _ => (T : ℝ) := by
    funext h
    exact_mod_cast sum_pullCount_univ h
  rw [this]
  simp

/-- The fraction of rounds in which an arm of `S` is pulled, and its expectation. -/
theorem integral_frac {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (S : Finset (Fin K)) :
    ∫ h, (∑ b ∈ S, (armPullCount b h : ℝ)) / (T : ℝ) ∂(banditMeasure ν π T) =
      (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) := by
  rw [integral_div, integral_finsetSum _ (fun i _ => integrable_pullCount ν π i)]
  rfl

theorem frac_mem {K : ℕ} (T : ℕ) (hT : 0 < T) (S : Finset (Fin K)) (h : BanditHistory K T) :
    (∑ b ∈ S, (armPullCount b h : ℝ)) / (T : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hTr]
  have := sum_pullCount_le S h
  exact_mod_cast this

theorem expFrac_mem {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (hT : 0 < T) (S : Finset (Fin K)) :
    (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← integral_frac]
  refine ⟨integral_nonneg (fun h => (frac_mem T hT S h).1), ?_⟩
  calc ∫ h, (∑ b ∈ S, (armPullCount b h : ℝ)) / (T : ℝ) ∂(banditMeasure ν π T)
      ≤ ∫ _h, (1 : ℝ) ∂(banditMeasure ν π T) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun h => (frac_mem T hT S h).1)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (fun h => (frac_mem T hT S h).2)
    _ = 1 := by simp

/-- Core change-of-measure inequality: combines the divergence decomposition, Lemma 1 applied
to `1 - Z`, and inequality (11). -/
theorem core {K : ℕ} (ν ν' : StochasticBandit K) (π : BanditPolicy K) (a : Fin K)
    (hrest : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k)
    (hKL : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 0 < T) (S : Finset (Fin K)) :
    (if (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ) = 0 ∧
        0 < (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) then (⊤ : ENNReal)
      else ENNReal.ofReal ((∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) *
          Real.log (1 / ((∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ))) -
          Real.log 2)) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) *
        InformationTheory.klDiv (ν.P a) (ν'.P a) := by
  set p := (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) with hp
  set q := (∑ b ∈ S, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ) with hq
  have hpm := expFrac_mem ν π T hT S
  have hqm := expFrac_mem ν' π T hT S
  rw [← hp] at hpm
  rw [← hq] at hqm
  -- KL finite on every arm
  have hKLall : ∀ i, InformationTheory.klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
    intro i
    by_cases hi : i = a
    · subst hi; exact hKL
    · rw [hrest i hi, InformationTheory.klDiv_self]; exact ENNReal.zero_ne_top
  have hdec := bandit_divergence_decomposition ν ν' hKLall π T
  have hsum : ∑ i, ENNReal.ofReal (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π T) *
        InformationTheory.klDiv (ν.P i) (ν'.P i) =
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) *
        InformationTheory.klDiv (ν.P a) (ν'.P a) := by
    rw [Finset.sum_eq_single a]
    · rfl
    · intro i _ hi
      rw [hrest i hi, InformationTheory.klDiv_self, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- Lemma 1 for W = 1 - Z
  set W : BanditHistory K T → ℝ := fun h => 1 - (∑ b ∈ S, (armPullCount b h : ℝ)) / (T : ℝ)
    with hW
  have hWm : Measurable W := by
    apply Measurable.const_sub
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => measurable_pullCount i)
  have hW01 : ∀ h, W h ∈ Set.Icc (0 : ℝ) 1 := by
    intro h
    have := frac_mem T hT S h
    exact ⟨by simp only [hW]; linarith [this.2], by simp only [hW]; linarith [this.1]⟩
  have hint : ∀ (μ : StochasticBandit K), ∫ h, W h ∂(banditMeasure μ π T) =
      1 - (∑ b ∈ S, ExploreFirst.FundIneq.expPulls μ π T b) / (T : ℝ) := by
    intro μ
    simp only [hW]
    rw [integral_sub (integrable_const _), integral_const, integral_frac]
    · simp
    · apply Integrable.div_const
      exact integrable_finsetSum _ (fun i _ => integrable_pullCount μ π i)
  have hL1 := ExploreFirst.FundIneq.lemma_1 (banditMeasure ν π T) (banditMeasure ν' π T)
    W hWm hW01
  rw [hint ν, hint ν', hdec, hsum] at hL1
  have h11 := ExploreFirst.Asymptotic.kl_ge_of_eq_11 (1 - p) (1 - q)
    ⟨by linarith [hpm.2], by linarith [hpm.1]⟩ ⟨by linarith [hqm.2], by linarith [hqm.1]⟩
  refine le_trans ?_ (h11.trans hL1)
  have e1 : (1 - q = 1 ∧ 1 - p < 1) ↔ (q = 0 ∧ 0 < p) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  by_cases hc : q = 0 ∧ 0 < p
  · rw [if_pos hc, if_pos (e1.2 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (e1.1 h))]
    simp

end EFCoreCOM

open EFCoreCOM ExploreFirst.LargeT

theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K) (C : ℝ)
    (hπ : IsUniformlySuperFast 𝒟 π C)
    (ν ν' : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (ha' : ν'.P a ∈ 𝒟)
    (hrest : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k)
    (hmean : banditOptimalMean ν < banditArmMean ν' a)
    (hKL : InformationTheory.klDiv (ν.P a) (ν'.P a) ≠ ⊤)
    (T : ℕ) (hT : 2 ≤ T) :
    (let EZ := (∑ b ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ)
     let EZ' := (∑ b ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ)
     (EZ * Real.log (1 / EZ') - Real.log 2) /
       (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by
  intro EZ EZ'
  have hc := core ν ν' π a hrest hKL T (by omega) (ExploreFirst.Asymptotic.optimalArms ν)
  have hE0 := expPulls_nonneg ν π T a
  set E := ExploreFirst.FundIneq.expPulls ν π T a
  set κ := (InformationTheory.klDiv (ν.P a) (ν'.P a)).toReal with hκ
  have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg
  have hrhs : ENNReal.ofReal E * InformationTheory.klDiv (ν.P a) (ν'.P a) =
      ENNReal.ofReal (E * κ) := by
    rw [ENNReal.ofReal_mul hE0, hκ, ENNReal.ofReal_toReal hKL]
  rw [hrhs] at hc
  by_cases hcase : EZ' = 0 ∧ 0 < EZ
  · rw [if_pos hcase] at hc
    exact absurd (top_le_iff.1 hc) ENNReal.ofReal_ne_top
  · rw [if_neg hcase] at hc
    have hX : EZ * Real.log (1 / EZ') - Real.log 2 ≤ E * κ :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hE0 hκ0)).1 hc
    rcases hκ0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]; linarith
    · rw [← hzero, div_zero]; exact hE0
