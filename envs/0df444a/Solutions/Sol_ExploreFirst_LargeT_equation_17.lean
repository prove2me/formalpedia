-- Prove2me | solution 1 for ExploreFirst.LargeT.equation_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:03:33.994769+00:00
-- url     : https://prove2.me/submissions/aff880a7-50e9-449d-aa34-3e03ecf7b3fc

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
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (ε : ℝ) (hε : 0 < ε)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε) ≠ ⊤)
    (T : ℕ) (hT : 2 ≤ T) (hC : 0 < C)
    (hb : C * hardness ν * Real.log T ≤ (T : ℝ)) :
    (let Kε := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)
     (1 - C * hardness ν * Real.log T / (T : ℝ)) *
       Real.log ((T : ℝ) * ε ^ 2 /
         ((ExploreFirst.Asymptotic.optimalArms ν).card * C * Real.log T)) / Kε.toReal -
       Real.log 2 / Kε.toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by
  intro Kε
  set μs := banditOptimalMean ν with hμs
  set L := Real.log (T : ℝ) with hL
  set opt := ExploreFirst.Asymptotic.optimalArms ν with hopt
  set A : ℝ := (opt.card : ℝ) with hA
  set E := ExploreFirst.FundIneq.expPulls ν π T a with hE
  set H := hardness ν with hH
  set β : ℝ := 1 - C * H * L / (T : ℝ) with hβ
  set B : ℝ := (T : ℝ) * ε ^ 2 / (A * C * L) with hB
  set κ := Kε.toReal with hκ
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hκpos : 0 < κ := ENNReal.toReal_pos hKpos.ne' hKfin
  have hE0 : 0 ≤ E := expPulls_nonneg ν π T a
  have hβ0 : 0 ≤ β := by
    rw [hβ, sub_nonneg, div_le_one hTpos]; exact hb
  -- optimal arms
  have hmean_le : ∀ i, banditArmMean ν i ≤ μs := fun i =>
    le_ciSup (Set.finite_range _).bddAbove i
  have hAne : opt.Nonempty := by
    haveI : Nonempty (Fin K) := ⟨a⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => banditArmMean ν i)
    refine ⟨i, ?_⟩
    simp only [hopt, ExploreFirst.Asymptotic.optimalArms, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hi
  have hA1 : (1 : ℝ) ≤ A := by
    have := Finset.card_pos.2 hAne
    rw [hA]; exact Nat.one_le_cast.2 this
  have hBpos : 0 < B := by positivity
  have hopt_mem : ∀ b, b ∈ opt ↔ banditArmMean ν b = μs := by
    intro b
    simp [hopt, ExploreFirst.Asymptotic.optimalArms, hμs]
  have haopt : a ∉ opt := by
    rw [hopt_mem]
    have : banditGap ν a = μs - banditArmMean ν a := rfl
    intro h; linarith
  -- rewrite the goal
  have hgoal : β * Real.log B / κ - Real.log 2 / κ = (β * Real.log B - Real.log 2) / κ := by
    ring
  show β * Real.log B / κ - Real.log 2 / κ ≤ E
  rw [hgoal]
  set N := β * Real.log B - Real.log 2 with hN
  by_cases hNpos : N ≤ 0
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hNpos hκpos.le) hE0
  push Not at hNpos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβpos : 0 < β := by
    rcases hβ0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [hN, ← h] at hNpos; linarith
  -- lower bound on the optimal fraction under ν
  have hp_ge : β ≤ (∑ b ∈ opt, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) := by
    have htot := sum_expPulls_univ ν π T
    rw [← Finset.sum_add_sum_compl opt] at htot
    have hsub : ∑ b ∈ optᶜ, ExploreFirst.FundIneq.expPulls ν π T b ≤ C * L * H := by
      rw [hH, hardness, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb'
      have hbn : b ∉ opt := Finset.mem_compl.1 hb'
      have hgap : 0 < banditGap ν b := by
        have : banditArmMean ν b ≠ μs := fun h => hbn ((hopt_mem b).2 h)
        have h2 := hmean_le b
        have : banditGap ν b = μs - banditArmMean ν b := rfl
        rw [this]; exact sub_pos.2 (lt_of_le_of_ne h2 (by assumption))
      have := hπ ν hν b hgap T hT
      calc _ ≤ C * Real.log T / banditGap ν b ^ 2 := this
        _ = C * L * (1 / banditGap ν b ^ 2) := by rw [hL]; ring
    rw [hβ, le_div_iff₀ hTpos]
    have : C * H * L / (T : ℝ) * T = C * L * H := by field_simp
    rw [sub_mul, this]
    linarith
  -- key claim for each alternative
  have claim : ∀ Q ∈ 𝒟, μs + ε < ∫ x, x ∂Q →
      InformationTheory.klDiv (ν.P a) Q ≠ ⊤ →
      N ≤ E * (InformationTheory.klDiv (ν.P a) Q).toReal := by
    intro Q hQ hQmean hQKL
    have hQprob : IsProbabilityMeasure Q := (h𝒟 Q hQ).1
    let ν' : StochasticBandit K := ⟨Function.update ν.P a Q, by
      intro i
      by_cases hi : i = a
      · subst hi; simp only [Function.update_self]; exact hQprob
      · rw [Function.update_of_ne hi]; exact ν.prob i⟩
    have hν'a : ν'.P a = Q := Function.update_self _ _ _
    have hrest : ∀ k : Fin K, k ≠ a → ν'.P k = ν.P k := fun k hk => Function.update_of_ne hk _ _
    have hν'model : ExploreFirst.Asymptotic.InModel 𝒟 ν' := by
      intro i
      by_cases hi : i = a
      · subst hi; rw [hν'a]; exact hQ
      · rw [hrest i hi]; exact hν i
    have hc := core ν ν' π a hrest (by rw [hν'a]; exact hQKL) T (by omega) opt
    rw [hν'a] at hc
    set p := (∑ b ∈ opt, ExploreFirst.FundIneq.expPulls ν π T b) / (T : ℝ) with hp
    set q := (∑ b ∈ opt, ExploreFirst.FundIneq.expPulls ν' π T b) / (T : ℝ) with hq
    have hqm := expFrac_mem ν' π T (by omega) opt
    rw [← hq] at hqm
    have hppos : 0 < p := lt_of_lt_of_le hβpos hp_ge
    have hκQ0 : 0 ≤ (InformationTheory.klDiv (ν.P a) Q).toReal := ENNReal.toReal_nonneg
    have hrhs : ENNReal.ofReal E * InformationTheory.klDiv (ν.P a) Q =
        ENNReal.ofReal (E * (InformationTheory.klDiv (ν.P a) Q).toReal) := by
      rw [ENNReal.ofReal_mul hE0, ENNReal.ofReal_toReal hQKL]
    rw [hrhs] at hc
    by_cases hcase : q = 0 ∧ 0 < p
    · rw [if_pos hcase] at hc
      exact absurd (top_le_iff.1 hc) ENNReal.ofReal_ne_top
    rw [if_neg hcase] at hc
    have hX := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hE0 hκQ0)).1 hc
    have hqpos : 0 < q := by
      rcases hqm.1.lt_or_eq with h | h
      · exact h
      · exact absurd ⟨h.symm, hppos⟩ hcase
    -- upper bound on q
    have hq_le : q ≤ 1 / B := by
      have hbound : ∀ b ∈ opt, ExploreFirst.FundIneq.expPulls ν' π T b ≤ C * L / ε ^ 2 := by
        intro b hb'
        have hba : b ≠ a := fun h => haopt (h ▸ hb')
        have hmb : banditArmMean ν' b = μs := by
          have : banditArmMean ν' b = banditArmMean ν b := by
            unfold banditArmMean; rw [hrest b hba]
          rw [this]; exact (hopt_mem b).1 hb'
        have hopt' : banditArmMean ν' a ≤ banditOptimalMean ν' :=
          le_ciSup (Set.finite_range _).bddAbove a
        have hma : banditArmMean ν' a = ∫ x, x ∂Q := by
          unfold banditArmMean; rw [hν'a]
        have hgap' : ε < banditGap ν' b := by
          have : banditGap ν' b = banditOptimalMean ν' - banditArmMean ν' b := rfl
          rw [this, hmb]; linarith
        have := hπ ν' hν'model b (lt_trans hε hgap') T hT
        refine le_trans this ?_
        rw [← hL]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hε.le hgap'.le 2
      have hsum : ∑ b ∈ opt, ExploreFirst.FundIneq.expPulls ν' π T b ≤ A * (C * L / ε ^ 2) := by
        calc _ ≤ ∑ _b ∈ opt, C * L / ε ^ 2 := Finset.sum_le_sum hbound
          _ = A * (C * L / ε ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hq, hB, div_le_iff₀ hTpos]
      calc _ ≤ A * (C * L / ε ^ 2) := hsum
        _ = 1 / ((T : ℝ) * ε ^ 2 / (A * C * L)) * T := by
          field_simp
    have hlogq : Real.log B ≤ Real.log (1 / q) := by
      apply Real.log_le_log hBpos
      rw [le_div_iff₀ hqpos]
      rw [le_div_iff₀ hBpos] at hq_le
      linarith
    have hlogq0 : 0 ≤ Real.log (1 / q) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hqpos]; linarith [hqm.2]
    have hpl : β * Real.log B ≤ p * Real.log (1 / q) := by
      rcases le_or_gt 0 (Real.log B) with h | h
      · exact mul_le_mul hp_ge hlogq h hppos.le
      · have : β * Real.log B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0 h.le
        linarith [mul_nonneg hppos.le hlogq0]
    rw [hN]; linarith
  -- infimum argument
  by_contra hcon
  push Not at hcon
  rw [lt_div_iff₀ hκpos] at hcon
  set δ : ℝ := (N - E * κ) / (E + 1) with hδ
  have hδpos : 0 < δ := by apply div_pos <;> linarith
  have hEδ : E * δ < N - E * κ := by
    rw [hδ, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hlt : Kε < ENNReal.ofReal (κ + δ) := by
    have hKfin' : Kε ≠ ⊤ := hKfin
    calc Kε = ENNReal.ofReal κ := (ENNReal.ofReal_toReal hKfin').symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hlt' := hlt
  simp only [Kε, banditDInf] at hlt'
  obtain ⟨Q, hQ'⟩ := iInf_lt_iff.1 hlt'
  obtain ⟨hQmem, hQlt⟩ := iInf_lt_iff.1 hQ'
  have hQKL : InformationTheory.klDiv (ν.P a) Q ≠ ⊤ := ne_top_of_lt hQlt
  have hQr : (InformationTheory.klDiv (ν.P a) Q).toReal < κ + δ := by
    have := (ENNReal.toReal_lt_toReal hQKL ENNReal.ofReal_ne_top).2 hQlt
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  have h1 := claim Q hQmem.1 hQmem.2 hQKL
  have h2 : E * (InformationTheory.klDiv (ν.P a) Q).toReal ≤ E * (κ + δ) :=
    mul_le_mul_of_nonneg_left hQr.le hE0
  linarith
