-- Prove2me | solution 1 for ExploreFirst.Asymptotic.alternative_others_little_o
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:00:22.601317+00:00
-- url     : https://prove2.me/submissions/6bc60668-214e-4676-beb9-f550873bd72c

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

open MeasureTheory BanditAlgorithm Filter

namespace EFA2Others

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

end EFA2Others

open ExploreFirst.Asymptotic EFA2Others

theorem solution {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (h𝒟 : IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : IsUniformlyFastConvergent 𝒟 π)
    (ν ν' : BanditAlgorithm.StochasticBandit K) (hν : InModel 𝒟 ν)
    (a : Fin K) (hother : ∀ k, k ≠ a → ν'.P k = ν.P k)
    (ha : ν'.P a ∈ 𝒟)
    (hbest : BanditAlgorithm.banditOptimalMean ν < BanditAlgorithm.banditArmMean ν' a)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ᶠ T : ℕ in Filter.atTop,
      (T : ℝ) - ExploreFirst.FundIneq.expPulls ν' π T a ≤ (T : ℝ) ^ α := by
  have hν' : InModel 𝒟 ν' := by
    intro k
    by_cases hk : k = a
    · subst hk; exact ha
    · rw [hother k hk]; exact hν k
  have hgap : ∀ k, k ≠ a → 0 < banditGap ν' k := by
    intro k hk
    unfold banditGap
    have h1 : banditArmMean ν' k = banditArmMean ν k := by
      unfold banditArmMean; rw [hother k hk]
    have h2 := armMean_le_opt ν k
    have h3 := armMean_le_opt ν' a
    linarith
  set S : Finset (Fin K) := Finset.univ.erase a
  have hlim : Tendsto (fun T : ℕ => ∑ k ∈ S, ExploreFirst.FundIneq.expPulls ν' π T k / (T : ℝ) ^ α)
      atTop (nhds 0) := by
    have := tendsto_finset_sum S (fun k hk => hπ ν' hν' k (hgap k (Finset.ne_of_mem_erase hk)) α hα hα1)
    simpa using this
  have hev := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  filter_upwards [hev, eventually_ge_atTop 1] with T hT hT1
  have hTpos : (0 : ℝ) < (T : ℝ) ^ α := by
    apply Real.rpow_pos_of_pos; exact_mod_cast hT1
  have hsum := sum_expPulls_univ ν' π T
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hsum
  rw [← Finset.sum_div] at hT
  rw [div_lt_one hTpos] at hT
  have : (T : ℝ) - ExploreFirst.FundIneq.expPulls ν' π T a = ∑ k ∈ S, ExploreFirst.FundIneq.expPulls ν' π T k := by
    linarith
  rw [this]
  exact hT.le
