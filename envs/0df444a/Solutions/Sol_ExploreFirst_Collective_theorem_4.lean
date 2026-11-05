-- Prove2me | solution 1 for ExploreFirst.Collective.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:35:24.584514+00:00
-- url     : https://prove2.me/submissions/7f248932-08b0-46d6-8919-ebd9f1e9b43f

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting
import Theorems.Thm_ExploreFirst_Collective_monotone_reduction
import Theorems.Thm_ExploreFirst_Collective_equation_14

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace EFCThm4Aux

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

end EFCThm4Aux

open EFCThm4Aux ExploreFirst.Collective in
theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (hmono : IsMonotonic 𝒟 π)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν) (hK : 0 < K) (hfin : kMax ν ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) * (1 - ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) / K
        - ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) * Real.sqrt (2 * T * (kMax ν).toReal) / K
        - 2 * ((ExploreFirst.Asymptotic.optimalArms ν).card : ℝ) * T * (kMax ν).toReal / K)
      ≤ ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms ν)ᶜ, ExploreFirst.FundIneq.expPulls ν π T a := by
  set S := ExploreFirst.Asymptotic.optimalArms ν with hS
  set k := (kMax ν).toReal with hk
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hsq0 : 0 ≤ Real.sqrt (2 * T * k) := Real.sqrt_nonneg _
  have hnn : ∀ (μ : StochasticBandit K) a, 0 ≤ ExploreFirst.FundIneq.expPulls μ π T a := fun μ a =>
    integral_nonneg (fun h => Nat.cast_nonneg _)
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hbdd : ∀ (μ : StochasticBandit K), BddAbove (Set.range (fun i => banditArmMean μ i)) :=
    fun μ => Set.finite_range _ |>.bddAbove
  -- a worst arm attaining the minimum in `kMax`
  have hWne : (worstArms ν).Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => banditArmMean ν i)
      Finset.univ_nonempty
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun b => hi b (Finset.mem_univ _)⟩⟩
  obtain ⟨w, hw, hwinf⟩ := Finset.exists_mem_eq_inf (worstArms ν) hWne
    (fun w => (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)))
  have hwmin : (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)) = kMax ν :=
    hwinf.symm
  have hwle : ∀ b, banditArmMean ν w ≤ banditArmMean ν b := (Finset.mem_filter.mp hw).2
  by_cases hwS : w ∈ S
  · -- all arms are optimal: the lower bound is nonpositive
    have hall : ∀ b, b ∈ S := by
      intro b
      have h1 : banditArmMean ν w = banditOptimalMean ν := (Finset.mem_filter.mp hwS).2
      have h2 : banditArmMean ν b ≤ banditOptimalMean ν := le_ciSup (hbdd ν) b
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h2 (h1 ▸ hwle b)⟩
    have hcard : (S.card : ℝ) = K := by
      have : S = Finset.univ := Finset.eq_univ_of_forall hall
      rw [this, Finset.card_univ, Fintype.card_fin]
    rw [hcard, div_self hKpos.ne']
    have hR : 0 ≤ ∑ a ∈ Sᶜ, ExploreFirst.FundIneq.expPulls ν π T a :=
      Finset.sum_nonneg (fun a _ => hnn ν a)
    have : (T : ℝ) * (1 - 1 - (K : ℝ) * Real.sqrt (2 * T * k) / K - 2 * (K : ℝ) * T * k / K) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hTpos.le
      have : 0 ≤ (K : ℝ) * Real.sqrt (2 * T * k) / K := by positivity
      have : 0 ≤ 2 * (K : ℝ) * T * k / K := by positivity
      linarith
    linarith
  -- the two auxiliary problems
  let νdd : StochasticBandit K :=
    ⟨fun a => if a ∈ S then ν.P a else ν.P w, fun a => by split_ifs <;> infer_instance⟩
  let νt : StochasticBandit K := ⟨fun _ => ν.P w, fun _ => inferInstance⟩
  have hνdd : ∀ a, νdd.P a = if a ∈ ExploreFirst.Asymptotic.optimalArms ν then ν.P a else ν.P w :=
    fun a => rfl
  have hνt : ∀ a, νt.P a = ν.P w := fun a => rfl
  have hνddM : ExploreFirst.Asymptotic.InModel 𝒟 νdd := by
    intro a
    rw [hνdd a]; split_ifs
    · exact hν a
    · exact hν w
  -- optimal arms of νdd are among those of ν
  have hsub : ExploreFirst.Asymptotic.optimalArms νdd ⊆ S := by
    intro a ha
    by_contra haS
    obtain ⟨s, hs⟩ : S.Nonempty := by
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => banditArmMean ν i)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have hmean : ∀ b, banditArmMean νdd b = if b ∈ S then banditArmMean ν b else banditArmMean ν w := by
      intro b
      unfold banditArmMean
      rw [hνdd b]; split_ifs <;> rfl
    have h1 : banditArmMean νdd a = banditOptimalMean νdd := (Finset.mem_filter.mp ha).2
    have h2 : banditArmMean νdd s ≤ banditOptimalMean νdd := le_ciSup (hbdd νdd) s
    rw [hmean a, if_neg haS] at h1
    rw [hmean s, if_pos hs, (Finset.mem_filter.mp hs).2] at h2
    have h3 : banditArmMean ν w ≤ banditOptimalMean ν := le_ciSup (hbdd ν) w
    exact hwS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h3 (h1 ▸ h2)⟩)
  have hmr := monotone_reduction 𝒟 h𝒟 π hmono ν hν w hw νdd hνdd T hT
  have h14 := equation_14 𝒟 h𝒟 π hπ ν hν hK w hw hwmin νdd hνdd νt hνt T hT hfin
  rw [div_le_iff₀ hTpos] at h14
  -- collect
  have htot := sum_expPulls νdd π T
  rw [← Finset.sum_compl_add_sum (ExploreFirst.Asymptotic.optimalArms νdd)] at htot
  have hsubsum : ∑ a ∈ ExploreFirst.Asymptotic.optimalArms νdd, ExploreFirst.FundIneq.expPulls νdd π T a
      ≤ ∑ a ∈ S, ExploreFirst.FundIneq.expPulls νdd π T a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hnn νdd a)
  have hgoal : (T : ℝ) * (1 - (S.card : ℝ) / K - (S.card : ℝ) * Real.sqrt (2 * T * k) / K
        - 2 * (S.card : ℝ) * T * k / K)
      = T - (S.card : ℝ) / K * (1 + 2 * T * k + Real.sqrt (2 * T * k)) * T := by
    field_simp
    ring
  rw [hgoal]
  linarith
