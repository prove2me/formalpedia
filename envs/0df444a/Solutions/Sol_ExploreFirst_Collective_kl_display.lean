-- Prove2me | solution 1 for ExploreFirst.Collective.kl_display
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:32:29.091215+00:00
-- url     : https://prove2.me/submissions/9b69754a-0cba-4560-a1c1-60877b006ab6

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting
import Theorems.Thm_ExploreFirst_Collective_uniform_split
import Theorems.Thm_ExploreFirst_FundIneq_lemma_1
import Theorems.Thm_BanditAlgorithm_bandit_divergence_decomposition

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace EFCKlDisplayAux

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

end EFCKlDisplayAux

open EFCKlDisplayAux in
theorem solution {K : ℕ}
    (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K)
    (w : Fin K) (hw : w ∈ ExploreFirst.Collective.worstArms ν)
    (hwmin : (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) = ExploreFirst.Collective.kMax ν)
    (νdd : StochasticBandit K)
    (hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w)
    (νt : StochasticBandit K) (hνt : ∀ a, νt.P a = ν.P w)
    (T : ℕ) (hT : 1 ≤ T) :
    ExploreFirst.FundIneq.klBer (((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K) ((∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls νdd π T a) / T)
      ≤ ENNReal.ofReal ((T : ℝ) * (ExploreFirst.Asymptotic.optimalArms ν).card / K) * ExploreFirst.Collective.kMax ν := by
  set S := ExploreFirst.Asymptotic.optimalArms ν with hS
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  -- `S` is nonempty
  have hSne : S.Nonempty := by
    haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => banditArmMean ν i)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  by_cases htop : ExploreFirst.Collective.kMax ν = ⊤
  · rw [htop, ENNReal.mul_top]
    · exact le_top
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      have : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
      positivity
  -- the KL terms
  have hKLle : ∀ a ∈ S, InformationTheory.klDiv (ν.P w) (ν.P a) ≤ ExploreFirst.Collective.kMax ν := by
    intro a ha
    rw [← hwmin]
    exact Finset.le_sup (f := fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) ha
  have hKLa : ∀ a, InformationTheory.klDiv (νt.P a) (νdd.P a) =
      if a ∈ S then InformationTheory.klDiv (ν.P w) (ν.P a) else 0 := by
    intro a
    rw [hνt a, hνdd a]
    split_ifs
    · rfl
    · exact InformationTheory.klDiv_self _
  have hKLfin : ∀ a, InformationTheory.klDiv (νt.P a) (νdd.P a) ≠ ⊤ := by
    intro a
    rw [hKLa a]
    split_ifs with ha
    · exact ne_top_of_le_ne_top htop (hKLle a ha)
    · exact ENNReal.zero_ne_top
  -- the test function
  set Z : BanditHistory K T → ℝ := fun h => (∑ a ∈ S, (armPullCount a h : ℝ)) / T with hZ
  have hZm : Measurable Z :=
    (Finset.measurable_sum _ (fun a _ => measurable_armPullCount_real a)).div_const _
  have hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1 := by
    intro h
    have hle : (∑ a ∈ S, (armPullCount a h : ℝ)) ≤ T := by
      have : (∑ a ∈ S, armPullCount a h) ≤ T := by
        calc (∑ a ∈ S, armPullCount a h) ≤ ∑ a : Fin K, armPullCount a h :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
          _ = T := sum_armPullCount h
      exact_mod_cast this
    refine ⟨div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hTpos.le, ?_⟩
    rw [div_le_one hTpos]; exact hle
  have hint : ∀ (μ : StochasticBandit K), ∫ h, Z h ∂(banditMeasure μ π T) =
      (∑ a ∈ S, ExploreFirst.FundIneq.expPulls μ π T a) / T := by
    intro μ
    rw [hZ, integral_div, integral_finsetSum _ (fun a _ => integrable_armPullCount μ π T a)]
    rfl
  -- uniform split under νt
  have hνtM : ExploreFirst.Asymptotic.InModel 𝒟 νt := fun a => by rw [hνt a]; exact hν w
  have hus : ∀ a, ExploreFirst.FundIneq.expPulls νt π T a = (T : ℝ) / K := fun a =>
    ExploreFirst.Collective.uniform_split 𝒟 h𝒟 π hπ νt hνtM (fun a b => by rw [hνt a, hνt b]) T hT a
  have hint1 : ∫ h, Z h ∂(banditMeasure νt π T) = (S.card : ℝ) / K := by
    rw [hint νt]
    simp_rw [hus, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have key := ExploreFirst.FundIneq.lemma_1 (banditMeasure νt π T) (banditMeasure νdd π T) Z hZm hZ01
  rw [hint1, hint νdd] at key
  refine key.trans ?_
  rw [BanditAlgorithm.bandit_divergence_decomposition νt νdd hKLfin π T]
  have hus' : ∀ a, ∫ h, (armPullCount a h : ℝ) ∂banditMeasure νt π T = (T : ℝ) / K := hus
  simp_rw [hus']
  calc ∑ a, ENNReal.ofReal ((T : ℝ) / K) * InformationTheory.klDiv (νt.P a) (νdd.P a)
      ≤ ∑ a, (if a ∈ S then ENNReal.ofReal ((T : ℝ) / K) * ExploreFirst.Collective.kMax ν else 0) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [hKLa a]
        split_ifs with ha
        · gcongr; exact hKLle a ha
        · simp
    _ = S.card • (ENNReal.ofReal ((T : ℝ) / K) * ExploreFirst.Collective.kMax ν) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
    _ = ENNReal.ofReal ((T : ℝ) * S.card / K) * ExploreFirst.Collective.kMax ν := by
        rw [nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [show (T : ℝ) * S.card / K = (S.card : ℝ) * (T / K) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
