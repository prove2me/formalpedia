-- Prove2me | solution 1 for ExploreFirst.Asymptotic.equation_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:03:49.995712+00:00
-- url     : https://prove2.me/submissions/fb7ca64b-89c2-4c82-a97e-be95d76b0b05

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition
import Theorems.Thm_ExploreFirst_FundIneq_lemma_1
import Theorems.Thm_ExploreFirst_Asymptotic_kl_ge_of_eq_11

open MeasureTheory BanditAlgorithm Filter
open scoped ENNReal

namespace EFA2Eq10

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

theorem sum_expPulls_univ {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) :
    ∑ b, ExploreFirst.FundIneq.expPulls ν π T b = T := by
  unfold ExploreFirst.FundIneq.expPulls
  rw [← integral_finsetSum _ (fun i _ => integrable_pullCount ν π i)]
  have : (fun h : BanditHistory K T => ∑ i, (armPullCount i h : ℝ)) = fun _ => (T : ℝ) := by
    funext h
    exact_mod_cast sum_pullCount_univ h
  rw [this]
  simp

theorem armMean_le_opt {K : ℕ} (ν : StochasticBandit K) (i : Fin K) :
    banditArmMean ν i ≤ banditOptimalMean ν :=
  le_ciSup (Set.finite_range _).bddAbove i

end EFA2Eq10

namespace EFA2Eq10

open InformationTheory NNReal

theorem expFrac_mem {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (hT : 0 < T) (a : Fin K) :
    ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hle : ExploreFirst.FundIneq.expPulls ν π T a ≤ T := by
    unfold ExploreFirst.FundIneq.expPulls
    calc ∫ h, (armPullCount a h : ℝ) ∂(banditMeasure ν π T)
        ≤ ∫ _h, (T : ℝ) ∂(banditMeasure ν π T) := by
          apply integral_mono (integrable_pullCount ν π a) (integrable_const _)
          intro h
          have := sum_pullCount_le {a} h
          simp at this
          show (armPullCount a h : ℝ) ≤ T
          exact_mod_cast this
      _ = T := by simp
  have h0 : 0 ≤ ExploreFirst.FundIneq.expPulls ν π T a :=
    integral_nonneg (fun _ => by positivity)
  exact ⟨by positivity, by rw [div_le_one hTr]; exact hle⟩

theorem klFun_le_one {y : ℝ} (h0 : 0 ≤ y) (h2 : y ≤ 2) : klFun y ≤ 1 := by
  unfold klFun
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · have hl := Real.log_le_sub_one_of_pos h
    have : y * Real.log y ≤ y * (y - 1) := mul_le_mul_of_nonneg_left hl h.le
    nlinarith

/-- If `μ ≤ N` (finite measures) then `KL(μ, N/2) < ∞`. -/
theorem kl_half_ne_top (μ N : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure N] (h : μ ≤ N) :
    klDiv μ ((2⁻¹ : ℝ≥0) • N) ≠ ⊤ := by
  have hr : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num
  have hNM : N ≪ (2⁻¹ : ℝ≥0) • N := by
    intro s hs
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at hs
    rcases hs with hs | hs
    · simp at hs
    · exact hs
  have hMN : (2⁻¹ : ℝ≥0) • N ≪ N := by
    intro s hs
    rw [Measure.smul_apply, hs, smul_zero]
  have hac : μ ≪ (2⁻¹ : ℝ≥0) • N := (Measure.absolutelyContinuous_of_le h).trans hNM
  have hbd : ∀ᵐ x ∂((2⁻¹ : ℝ≥0) • N), μ.rnDeriv ((2⁻¹ : ℝ≥0) • N) x ≤ 2 := by
    apply hMN.ae_le
    filter_upwards [Measure.rnDeriv_smul_right μ N hr, Measure.rnDeriv_le_one_of_le h] with x hx h1
    rw [hx]
    simp only [Pi.smul_apply, inv_inv, Pi.one_apply] at h1 ⊢
    rw [ENNReal.smul_def, smul_eq_mul]
    calc ((2 : ℝ≥0) : ℝ≥0∞) * μ.rnDeriv N x ≤ ((2 : ℝ≥0) : ℝ≥0∞) * 1 := by gcongr
      _ = 2 := by simp
  rw [klDiv_ne_top_iff]
  refine ⟨hac, (integrable_klFun_rnDeriv_iff hac).1 ?_⟩
  apply Integrable.of_bound (C := 1)
  · exact (continuous_klFun.measurable.comp
      (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable
  · filter_upwards [hbd, Measure.rnDeriv_lt_top μ ((2⁻¹ : ℝ≥0) • N)] with x hx hfin
    have h0 : 0 ≤ (μ.rnDeriv ((2⁻¹ : ℝ≥0) • N) x).toReal := ENNReal.toReal_nonneg
    have h2 : (μ.rnDeriv ((2⁻¹ : ℝ≥0) • N) x).toReal ≤ 2 := by
      have := ENNReal.toReal_mono (by simp) hx
      simpa using this
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg h0)]
    exact klFun_le_one h0 h2

end EFA2Eq10

open ExploreFirst.Asymptotic EFA2Eq10 InformationTheory NNReal

theorem solution {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (π : BanditAlgorithm.BanditPolicy K) (a : Fin K) (T : ℕ)
    (hT : 1 ≤ T) (hother : ∀ k, k ≠ a → ν'.P k = ν.P k) :
    ExploreFirst.FundIneq.klBer (ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) (ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ)) ≤
      ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a) * InformationTheory.klDiv (ν.P a) (ν'.P a) ∧
    (if ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ) = 1 ∧
        ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ) < 1 then (⊤ : ENNReal)
      else ENNReal.ofReal
        ((1 - ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) *
          Real.log ((T : ℝ) / ((T : ℝ) - ExploreFirst.FundIneq.expPulls ν' π T a)) - Real.log 2)) ≤
      ExploreFirst.FundIneq.klBer (ExploreFirst.FundIneq.expPulls ν π T a / (T : ℝ)) (ExploreFirst.FundIneq.expPulls ν' π T a / (T : ℝ)) := by
  have hT0 : 0 < T := hT
  have hTr : (T : ℝ) ≠ 0 := by positivity
  set E := ExploreFirst.FundIneq.expPulls ν π T a with hEdef
  set E' := ExploreFirst.FundIneq.expPulls ν' π T a with hE'def
  have hp := expFrac_mem ν π T hT0 a
  have hq := expFrac_mem ν' π T hT0 a
  rw [← hEdef] at hp
  rw [← hE'def] at hq
  refine ⟨?_, ?_⟩
  · by_cases hKL : klDiv (ν.P a) (ν'.P a) = ⊤
    · by_cases hE : E = 0
      · -- degenerate case: arm `a` is a.s. never pulled under `ν`, hence under `ν'`
        have hprobN : IsProbabilityMeasure ((2⁻¹ : ℝ≥0) • (ν.P a + ν'.P a)) := by
          constructor
          rw [Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ,
            ENNReal.smul_def, smul_eq_mul]
          rw [show (1 : ℝ≥0∞) + 1 = ((2 : ℝ≥0) : ℝ≥0∞) by norm_num, ← ENNReal.coe_mul]
          norm_num
        let ν'' : BanditAlgorithm.StochasticBandit K :=
          { P := Function.update ν.P a ((2⁻¹ : ℝ≥0) • (ν.P a + ν'.P a))
            prob := by
              intro i
              by_cases hi : i = a
              · subst hi; simpa using hprobN
              · rw [Function.update_of_ne hi]; exact ν.prob i }
        have hPa : ν''.P a = (2⁻¹ : ℝ≥0) • (ν.P a + ν'.P a) := by simp [ν'']
        have hPo : ∀ i, i ≠ a → ν''.P i = ν.P i := fun i hi => by
          simp [ν'', Function.update_of_ne hi]
        have hK1 : klDiv (ν.P a) (ν''.P a) ≠ ⊤ := by
          rw [hPa]; exact kl_half_ne_top _ _ (Measure.le_add_right le_rfl)
        have hK2 : klDiv (ν'.P a) (ν''.P a) ≠ ⊤ := by
          rw [hPa]; exact kl_half_ne_top _ _ (Measure.le_add_left le_rfl)
        have hall1 : ∀ i, klDiv (ν.P i) (ν''.P i) ≠ ⊤ := by
          intro i
          by_cases hi : i = a
          · subst hi; exact hK1
          · rw [hPo i hi, klDiv_self]; exact ENNReal.zero_ne_top
        have hall2 : ∀ i, klDiv (ν'.P i) (ν''.P i) ≠ ⊤ := by
          intro i
          by_cases hi : i = a
          · subst hi; exact hK2
          · rw [hPo i hi, hother i hi, klDiv_self]; exact ENNReal.zero_ne_top
        have d1 := BanditAlgorithm.bandit_divergence_decomposition ν ν'' hall1 π T
        have d2 := BanditAlgorithm.bandit_divergence_decomposition ν' ν'' hall2 π T
        have hzero : klDiv (banditMeasure ν π T) (banditMeasure ν'' π T) = 0 := by
          rw [d1]
          apply Finset.sum_eq_zero
          intro i _
          by_cases hi : i = a
          · subst hi
            have : (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π T) = 0 := hE
            rw [this, ENNReal.ofReal_zero, zero_mul]
          · rw [hPo i hi, klDiv_self, mul_zero]
        have heq : banditMeasure ν π T = banditMeasure ν'' π T := klDiv_eq_zero_iff.1 hzero
        have hfin : klDiv (banditMeasure ν' π T) (banditMeasure ν'' π T) ≠ ⊤ := by
          rw [d2]
          exact ENNReal.sum_ne_top.2 (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hall2 i))
        have hac : banditMeasure ν' π T ≪ banditMeasure ν π T := by
          rw [heq]; exact (klDiv_ne_top_iff.1 hfin).1
        have hz : (fun h : BanditHistory K T => (armPullCount a h : ℝ)) =ᵐ[banditMeasure ν π T] 0 :=
          (integral_eq_zero_iff_of_nonneg (fun _ => by positivity)
            (integrable_pullCount ν π a)).1 hE
        have hE' : E' = 0 := by
          rw [hE'def]
          unfold ExploreFirst.FundIneq.expPulls
          rw [integral_congr_ae (hac.ae_le hz)]
          simp
        rw [hE, hE', zero_div]
        have : IsFiniteMeasure (ExploreFirst.FundIneq.bernoulliLaw 0) := by
          unfold ExploreFirst.FundIneq.bernoulliLaw
          constructor
          simp
        unfold ExploreFirst.FundIneq.klBer
        rw [klDiv_self]
        exact zero_le
      · have hEpos : 0 < E := lt_of_le_of_ne (by
          have := hp.1; rwa [le_div_iff₀ (by positivity), zero_mul] at this) (Ne.symm hE)
        rw [hKL, ENNReal.mul_top (by simpa using hEpos)]
        exact le_top
    · have hKLall : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
        intro i
        by_cases hi : i = a
        · subst hi; exact hKL
        · rw [hother i hi, klDiv_self]; exact ENNReal.zero_ne_top
      have hdec := BanditAlgorithm.bandit_divergence_decomposition ν ν' hKLall π T
      have hsum : ∑ i, ENNReal.ofReal (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π T) *
            klDiv (ν.P i) (ν'.P i) = ENNReal.ofReal E * klDiv (ν.P a) (ν'.P a) := by
        rw [Finset.sum_eq_single a]
        · rfl
        · intro i _ hi
          rw [hother i hi, klDiv_self, mul_zero]
        · intro h; exact absurd (Finset.mem_univ a) h
      set Z : BanditHistory K T → ℝ := fun h => (armPullCount a h : ℝ) / (T : ℝ) with hZ
      have hZm : Measurable Z := (measurable_pullCount a).div_const _
      have hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1 := by
        intro h
        have hTpos : (0 : ℝ) < T := by positivity
        refine ⟨by positivity, ?_⟩
        rw [hZ, div_le_one hTpos]
        have := sum_pullCount_le {a} h
        simp at this
        exact_mod_cast this
      have hint : ∀ μ : StochasticBandit K, ∫ h, Z h ∂(banditMeasure μ π T) =
          ExploreFirst.FundIneq.expPulls μ π T a / (T : ℝ) := by
        intro μ
        rw [hZ, integral_div]
        rfl
      have hL1 := ExploreFirst.FundIneq.lemma_1 (banditMeasure ν π T) (banditMeasure ν' π T)
        Z hZm hZ01
      rw [hint ν, hint ν', hdec, hsum] at hL1
      exact hL1
  · have h11 := ExploreFirst.Asymptotic.kl_ge_of_eq_11 (E / (T : ℝ)) (E' / (T : ℝ)) hp hq
    have hrw : (1 : ℝ) / (1 - E' / (T : ℝ)) = (T : ℝ) / ((T : ℝ) - E') := by
      rw [show (1 : ℝ) - E' / (T : ℝ) = ((T : ℝ) - E') / (T : ℝ) by field_simp, one_div_div]
    rw [hrw] at h11
    exact h11
