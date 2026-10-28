-- Prove2me | solution 1 for ExploreFirst.Relative.symmetry_half
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:59:37.135373+00:00
-- url     : https://prove2.me/submissions/bdc4dbac-bbcf-486c-bb2b-dc1c7c5f9fd8

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Relative_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace Aux_ExploreFirst_Relative_symmetry_half

lemma meas_count {K T : ℕ} (b : Fin K) :
    Measurable (fun h : BanditHistory K T => armPullCount b h) := by
  have h1 : Measurable (fun h : BanditHistory K T => fun t => (h t).1) :=
    measurable_pi_lambda _ (fun t => measurable_fst.comp (measurable_pi_apply t))
  have h2 : Measurable (fun g : Fin T → Fin K => ({t | g t = b} : Set (Fin T)).toFinset.card) :=
    measurable_of_countable _
  exact h2.comp h1

noncomputable def fr (p q : ℕ) : ℝ := max (p : ℝ) 1 / (max (p : ℝ) 1 + max (q : ℝ) 1)

lemma fr_bounds (p q : ℕ) : 0 ≤ fr p q ∧ fr p q ≤ 1 := by
  unfold fr
  have h1 : (1 : ℝ) ≤ max (p : ℝ) 1 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ max (q : ℝ) 1 := le_max_right _ _
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

lemma fr_add (p q : ℕ) : fr p q + fr q p = 1 := by
  unfold fr
  have h1 : (1 : ℝ) ≤ max (p : ℝ) 1 := le_max_right _ _
  have h2 : (1 : ℝ) ≤ max (q : ℝ) 1 := le_max_right _ _
  rw [add_comm (max (q : ℝ) 1) (max (p : ℝ) 1), ← add_div, div_self (by linarith)]

end Aux_ExploreFirst_Relative_symmetry_half

open Aux_ExploreFirst_Relative_symmetry_half in
open ExploreFirst.Relative in
theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (π : BanditPolicy K) (hπ : IsPairwiseSymmetric 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a a' : Fin K) (ha : 0 < banditGap ν a) (ha' : a' ∈ ExploreFirst.Asymptotic.optimalArms ν)
    (ν' : StochasticBandit K) (hν'_ne : ∀ k, k ≠ a → ν'.P k = ν.P k) (hν'_a : ν'.P a = ν.P a')
    (T : ℕ) (hT : 1 ≤ T) :
    (∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂(banditMeasure ν' π T) =
      ∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂(banditMeasure ν' π T)) ∧
    (∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂(banditMeasure ν' π T) = 1 / 2) := by
  have hne : Nonempty (Fin K) := ⟨a⟩
  simp only [ExploreFirst.Asymptotic.optimalArms, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha'
  have haa' : a ≠ a' := by
    intro h
    subst h
    unfold banditGap at ha
    linarith
  have hmean : ∀ k, banditArmMean ν' k = if k = a then banditArmMean ν a' else banditArmMean ν k := by
    intro k
    by_cases hk : k = a
    · subst hk; rw [if_pos rfl]; unfold banditArmMean; rw [hν'_a]
    · rw [if_neg hk]; unfold banditArmMean; rw [hν'_ne k hk]
  have hbdd : ∀ (μ : StochasticBandit K), BddAbove (Set.range (banditArmMean μ)) :=
    fun μ => (Set.finite_range _).bddAbove
  have hopt : banditOptimalMean ν' = banditOptimalMean ν := by
    apply le_antisymm
    · unfold banditOptimalMean
      apply ciSup_le
      intro k
      rw [hmean]
      split_ifs
      · exact le_ciSup (hbdd ν) a'
      · exact le_ciSup (hbdd ν) k
    · calc banditOptimalMean ν = banditArmMean ν a' := ha'.symm
        _ = banditArmMean ν' a' := by rw [hmean, if_neg (Ne.symm haa')]
        _ ≤ banditOptimalMean ν' := le_ciSup (hbdd ν') a'
  have hopt_a : banditArmMean ν' a = banditOptimalMean ν' := by
    rw [hopt, hmean, if_pos rfl, ha']
  have hopt_a' : banditArmMean ν' a' = banditOptimalMean ν' := by
    rw [hopt, hmean, if_neg (Ne.symm haa'), ha']
  have hin : ExploreFirst.Asymptotic.InModel 𝒟 ν' := by
    intro k
    by_cases hk : k = a
    · subst hk; rw [hν'_a]; exact hν a'
    · rw [hν'_ne k hk]; exact hν k
  have hPeq : ν'.P a = ν'.P a' := by rw [hν'_a, hν'_ne a' (Ne.symm haa')]
  have hsym := hπ ν' hin a (by simp [ExploreFirst.Asymptotic.optimalArms, hopt_a]) a'
    (by simp [ExploreFirst.Asymptotic.optimalArms, hopt_a']) hPeq T hT
  set μ := banditMeasure ν' π T with hμ
  have hφ1 : Measurable (fun h : BanditHistory K T => (armPullCount a h, armPullCount a' h)) :=
    (meas_count a).prodMk (meas_count a')
  have hφ2 : Measurable (fun h : BanditHistory K T => (armPullCount a' h, armPullCount a h)) :=
    (meas_count a').prodMk (meas_count a)
  have hg : Measurable (fun p : ℕ × ℕ => fr p.1 p.2) := measurable_of_countable _
  have hfeq : ∀ b c : Fin K,
      (fun h : BanditHistory K T => pullsPlus b h / (pullsPlus b h + pullsPlus c h)) =
        fun h => fr (armPullCount b h) (armPullCount c h) := by
    intro b c
    funext h
    simp only [fr, pullsPlus]
  have e1 : ∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂μ =
      ∫ p, fr p.1 p.2 ∂(μ.map (fun h => (armPullCount a h, armPullCount a' h))) := by
    rw [integral_map hφ1.aemeasurable hg.aestronglyMeasurable, hfeq a a']
  have e2 : ∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂μ =
      ∫ p, fr p.1 p.2 ∂(μ.map (fun h => (armPullCount a' h, armPullCount a h))) := by
    rw [integral_map hφ2.aemeasurable hg.aestronglyMeasurable, hfeq a' a]
  have c1 : ∫ h, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) ∂μ =
      ∫ h, pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) ∂μ := by
    rw [e1, e2, hsym]
  refine ⟨c1, ?_⟩
  have hint : ∀ (b c : Fin K), Integrable
      (fun h : BanditHistory K T => pullsPlus b h / (pullsPlus b h + pullsPlus c h)) μ := by
    intro b c
    rw [hfeq b c]
    have hm : Measurable ((fun p : ℕ × ℕ => fr p.1 p.2) ∘
        (fun h : BanditHistory K T => (armPullCount b h, armPullCount c h))) :=
      hg.comp ((meas_count b).prodMk (meas_count c))
    have hm' : AEStronglyMeasurable
        (fun h : BanditHistory K T => fr (armPullCount b h) (armPullCount c h)) μ :=
      hm.aestronglyMeasurable
    refine Integrable.of_bound hm' 1
      (Filter.Eventually.of_forall (fun h => ?_))
    have := fr_bounds (armPullCount b h) (armPullCount c h)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  have hsum : ∫ h, (pullsPlus a h / (pullsPlus a h + pullsPlus a' h) +
      pullsPlus a' h / (pullsPlus a' h + pullsPlus a h)) ∂μ = 1 := by
    have : ∀ h : BanditHistory K T, pullsPlus a h / (pullsPlus a h + pullsPlus a' h) +
        pullsPlus a' h / (pullsPlus a' h + pullsPlus a h) = 1 := by
      intro h
      have := fr_add (armPullCount a h) (armPullCount a' h)
      simpa only [fr, pullsPlus] using this
    simp only [this, integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [integral_add (hint a a') (hint a' a), c1] at hsum
  linarith
