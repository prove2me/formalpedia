-- Prove2me | solution 1 for ExploreFirst.Collective.monotone_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:18:54.607036+00:00
-- url     : https://prove2.me/submissions/e4cdc669-83fa-477e-9616-595426f50502

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace Aux_ExploreFirst_Collective_monotone_reduction

lemma meas_count {K T : ℕ} (b : Fin K) :
    Measurable (fun h : BanditHistory K T => armPullCount b h) := by
  have h1 : Measurable (fun h : BanditHistory K T => fun t => (h t).1) :=
    measurable_pi_lambda _ (fun t => measurable_fst.comp (measurable_pi_apply t))
  have h2 : Measurable (fun g : Fin T → Fin K => ({t | g t = b} : Set (Fin T)).toFinset.card) :=
    measurable_of_countable _
  exact h2.comp h1

lemma sum_counts {K T : ℕ} (h : BanditHistory K T) :
    ∑ a : Fin K, (armPullCount a h : ℝ) = T := by
  classical
  have : ∑ a : Fin K, armPullCount a h = T := by
    unfold armPullCount
    simp only [Set.toFinset_setOf]
    rw [← Finset.card_eq_sum_card_fiberwise (fun t _ => Finset.mem_univ ((h t).1))]
    simp
  exact_mod_cast this

lemma total_pulls {K : ℕ} (μ : StochasticBandit K) (π : BanditPolicy K) (T : ℕ) :
    ∑ a : Fin K, ExploreFirst.FundIneq.expPulls μ π T a = T := by
  unfold ExploreFirst.FundIneq.expPulls
  have hint : ∀ a ∈ (Finset.univ : Finset (Fin K)),
      Integrable (fun h : BanditHistory K T => (armPullCount a h : ℝ)) (banditMeasure μ π T) := by
    intro a _
    refine Integrable.of_bound (measurable_from_nat.comp (meas_count a)).aestronglyMeasurable
      (T : ℝ) (Filter.Eventually.of_forall (fun h => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have : armPullCount a h ≤ T := by
      unfold armPullCount
      calc _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_le_univ _
        _ = T := Finset.card_fin T
    exact_mod_cast this
  rw [← integral_finset_sum _ hint]
  simp only [sum_counts]
  simp

end Aux_ExploreFirst_Collective_monotone_reduction

open Aux_ExploreFirst_Collective_monotone_reduction in
open ExploreFirst.Collective in
theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hmono : IsMonotonic 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (w : Fin K) (hw : w ∈ worstArms ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms νdd)ᶜ, ExploreFirst.FundIneq.expPulls νdd π T a ≤ ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms ν)ᶜ, ExploreFirst.FundIneq.expPulls ν π T a := by
  have hin : ExploreFirst.Asymptotic.InModel 𝒟 νdd := by
    intro a
    rw [hνdd a]
    split_ifs
    · exact hν a
    · exact hν w
  have hprec : Precedes νdd ν := by
    refine ⟨fun a ha => by rw [hνdd a, if_pos ha], fun a ha => ?_⟩
    have hmean : banditArmMean νdd a = banditArmMean ν w := by
      unfold banditArmMean; rw [hνdd a, if_neg ha]
    rw [hmean]
    exact (Finset.mem_filter.1 hw).2 a
  have hm := hmono ν νdd hν hin hprec T hT
  have h1 := Finset.sum_compl_add_sum (ExploreFirst.Asymptotic.optimalArms νdd)
    (fun a => ExploreFirst.FundIneq.expPulls νdd π T a)
  have h2 := Finset.sum_compl_add_sum (ExploreFirst.Asymptotic.optimalArms ν)
    (fun a => ExploreFirst.FundIneq.expPulls ν π T a)
  rw [total_pulls] at h1 h2
  linarith
