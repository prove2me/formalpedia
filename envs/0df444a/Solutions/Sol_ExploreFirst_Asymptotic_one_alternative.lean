-- Prove2me | solution 1 for ExploreFirst.Asymptotic.one_alternative
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:06:29.356807+00:00
-- url     : https://prove2.me/submissions/739dfe8e-10b8-41a0-aa60-bc32a09aa48c

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Theorems.Thm_ExploreFirst_Asymptotic_equation_10
import Theorems.Thm_ExploreFirst_Asymptotic_alternative_others_little_o

open MeasureTheory BanditAlgorithm Filter
open scoped ENNReal

namespace EFA2One

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

end EFA2One

namespace EFA2One

theorem expPulls_mem {K : ℕ} (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) (a : Fin K) :
    0 ≤ ExploreFirst.FundIneq.expPulls ν π T a ∧ ExploreFirst.FundIneq.expPulls ν π T a ≤ T := by
  refine ⟨integral_nonneg (fun _ => by positivity), ?_⟩
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

end EFA2One

open ExploreFirst.Asymptotic EFA2One InformationTheory

theorem solution {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hsub : 0 < BanditAlgorithm.banditGap ν a)
    (hother : ∀ k, k ≠ a → ν'.P k = ν.P k)
    (ha : ν'.P a ∈ 𝒟)
    (hbest : BanditAlgorithm.banditOptimalMean ν < BanditAlgorithm.banditArmMean ν' a) :
    (InformationTheory.klDiv (ν.P a) (ν'.P a))⁻¹ ≤
      Filter.liminf (fun T : ℕ =>
        ENNReal.ofReal (ExploreFirst.FundIneq.expPulls ν π T a / Real.log T)) Filter.atTop := by
  set KL := InformationTheory.klDiv (ν.P a) (ν'.P a) with hKLdef
  by_cases htop : KL = ⊤
  · rw [htop, ENNReal.inv_top]; exact zero_le
  have hne0 : KL ≠ 0 := by
    intro h0
    have heq : ν.P a = ν'.P a := klDiv_eq_zero_iff.1 h0
    have h1 : banditArmMean ν' a = banditArmMean ν a := by
      unfold banditArmMean; rw [heq]
    have h2 : banditArmMean ν a ≤ banditOptimalMean ν :=
      le_ciSup (Set.finite_range _).bddAbove a
    linarith
  set k := KL.toReal with hkdef
  have hkpos : 0 < k := ENNReal.toReal_pos hne0 htop
  have hKLk : KL = ENNReal.ofReal k := (ENNReal.ofReal_toReal htop).symm
  -- notation
  set E : ℕ → ℝ := fun T => ExploreFirst.FundIneq.expPulls ν π T a with hEdef
  set E' : ℕ → ℝ := fun T => ExploreFirst.FundIneq.expPulls ν' π T a with hE'def
  -- `E_T / T → 0`
  have hp0 : Tendsto (fun T : ℕ => E T / (T : ℝ)) atTop (nhds 0) := by
    have := hπ ν hν a hsub 1 one_pos le_rfl
    simpa [Real.rpow_one] using this
  -- key real claim
  have key : ∀ c : ℝ, c < 1 / k → ∀ᶠ T : ℕ in atTop, c ≤ E T / Real.log T := by
    intro c hc
    set δ := 1 / k - c with hδ
    have hδpos : 0 < δ := by linarith
    set α := min 1 (k * δ / 2) with hαdef
    have hαpos : 0 < α := lt_min one_pos (by positivity)
    have hα1 : α ≤ 1 := min_le_left _ _
    have hαle : α ≤ k * δ / 2 := min_le_right _ _
    have hlim : Tendsto (fun T : ℕ => ((1 - E T / T) * (1 - α) - Real.log 2 / Real.log T) / k)
        atTop (nhds (((1 - 0) * (1 - α) - 0) / k)) := by
      have hlog : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun T : ℕ => Real.log 2 / Real.log T) atTop (nhds 0) :=
        hlog.const_div_atTop _
      exact ((((tendsto_const_nhds.sub hp0).mul tendsto_const_nhds).sub h2).div_const k)
    have hgt : c < ((1 - 0) * (1 - α) - 0) / k := by
      rw [lt_div_iff₀ hkpos]
      have : c * k = 1 - δ * k := by rw [hδ]; field_simp; ring
      nlinarith
    have hev1 := hlim.eventually (lt_mem_nhds hgt)
    have hev2 := alternative_others_little_o 𝒟 h𝒟 π hπ ν ν' hν a hother ha hbest α hαpos hα1
    filter_upwards [hev1, hev2, eventually_ge_atTop 2] with T h1 h2 hT2
    refine h1.le.trans ?_
    have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT2
    have hTpos : (0 : ℝ) < T := by linarith
    have hlogpos : 0 < Real.log (T : ℝ) := Real.log_pos (by linarith)
    obtain ⟨hE0, hET⟩ := expPulls_mem ν π T a
    obtain ⟨hE'0, hE'T⟩ := expPulls_mem ν' π T a
    have hp1 : E T / T ≤ 1 := by rw [div_le_one hTpos]; exact hET
    -- the real inequality `E k ≥ (1-p)(1-α) ln T - ln 2`
    have hmain : (1 - E T / T) * (1 - α) * Real.log T - Real.log 2 ≤ E T * k := by
      have heq10 := equation_10 ν ν' π a T (by omega) hother
      obtain ⟨hA, hB⟩ := heq10
      have hchain := hB.trans hA
      rw [← hKLdef, hKLk, ← ENNReal.ofReal_mul hE0] at hchain
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rcases (lt_or_eq_of_le hE'T) with hlt | heqT
      · -- `E' < T`
        have hq : ¬ (E' T / (T : ℝ) = 1 ∧ E T / (T : ℝ) < 1) := by
          rintro ⟨hq1, -⟩
          rw [div_eq_one_iff_eq hTpos.ne'] at hq1
          exact absurd hq1 hlt.ne
        simp only [hE'def, hEdef] at hq hchain
        rw [if_neg hq] at hchain
        have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
        have hpos : 0 < (T : ℝ) - E' T := by linarith
        have hle : (T : ℝ) - E' T ≤ (T : ℝ) ^ α := h2
        have hlogle : (1 - α) * Real.log T ≤ Real.log ((T : ℝ) / ((T : ℝ) - E' T)) := by
          rw [Real.log_div hTpos.ne' hpos.ne']
          have := Real.log_le_log hpos hle
          rw [Real.log_rpow hTpos] at this
          linarith
        have h1p : 0 ≤ 1 - E T / T := by linarith
        have := mul_le_mul_of_nonneg_left hlogle h1p
        simp only [hEdef, hE'def] at this ⊢
        nlinarith
      · -- `E' = T`: then `E = T` as well
        have hpeq : E T / T = 1 := by
          by_contra hne
          have hplt : E T / T < 1 := lt_of_le_of_ne hp1 hne
          have hq : E' T / (T : ℝ) = 1 ∧ E T / (T : ℝ) < 1 :=
            ⟨(div_eq_one_iff_eq hTpos.ne').2 heqT, hplt⟩
          simp only [hE'def, hEdef] at hq hchain
          rw [if_pos hq] at hchain
          exact ENNReal.ofReal_ne_top (top_le_iff.1 hchain)
        rw [hpeq]
        have : 0 ≤ E T * k := by positivity
        nlinarith
    rw [le_div_iff₀ hlogpos, div_mul_eq_mul_div, div_le_iff₀ hkpos]
    have hcan : Real.log 2 / Real.log T * Real.log T = Real.log 2 := div_mul_cancel₀ _ hlogpos.ne'
    rw [sub_mul, hcan]
    linarith [hmain]
  -- conclude
  rw [hKLk, ← ENNReal.ofReal_inv_of_pos hkpos]
  refine le_of_forall_lt_imp_le_of_dense fun x hx => ?_
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx
  have hxr : x.toReal < 1 / k := by
    rw [one_div]
    exact (ENNReal.toReal_lt_of_lt_ofReal hx)
  rw [← ENNReal.ofReal_toReal hxtop]
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [key _ hxr] with T hT
  exact ENNReal.ofReal_le_ofReal hT
