-- Prove2me | solution 1 for ExploreFirst.Collective.uniform_split
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:30:40.240837+00:00
-- url     : https://prove2.me/submissions/fdbe75e0-16c0-438a-9d7a-6ac93babae73

import Mathlib
import Definitions.Def_ExploreFirst_Collective_Setting

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

namespace EFCUniformSplitAux

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

end EFCUniformSplitAux

open EFCUniformSplitAux in
theorem solution {K : ℕ} (𝒟 : Set (Measure ℝ)) (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K)
    (hπ : ExploreFirst.Relative.IsPairwiseSymmetric 𝒟 π) (νt : StochasticBandit K) (hνt : ExploreFirst.Asymptotic.InModel 𝒟 νt)
    (hsame : ∀ a b, νt.P a = νt.P b) (T : ℕ) (hT : 1 ≤ T) (a : Fin K) :
    ExploreFirst.FundIneq.expPulls νt π T a = (T : ℝ) / K := by
  have : Nonempty (Fin K) := ⟨a⟩
  have hmean : ∀ i, banditArmMean νt i = banditArmMean νt a := by
    intro i; simp [banditArmMean, hsame i a]
  have hopt : ∀ i, i ∈ ExploreFirst.Asymptotic.optimalArms νt := by
    intro i
    simp only [ExploreFirst.Asymptotic.optimalArms, Finset.mem_filter, Finset.mem_univ, true_and,
      banditOptimalMean, hmean, ciSup_const]
  have heq : ∀ b, ExploreFirst.FundIneq.expPulls νt π T b = ExploreFirst.FundIneq.expPulls νt π T a := by
    intro b
    have hmap := hπ νt hνt b (hopt b) a (hopt a) (hsame b a) T hT
    have hf : ∀ (c d : Fin K), Measurable (fun h : BanditHistory K T => (armPullCount c h, armPullCount d h)) :=
      fun c d => (measurable_armPullCount c).prodMk (measurable_armPullCount d)
    have hg : Measurable (fun p : ℕ × ℕ => (p.1 : ℝ)) := measurable_of_countable _
    have e1 : ExploreFirst.FundIneq.expPulls νt π T b =
        ∫ p, (p.1 : ℝ) ∂((banditMeasure νt π T).map (fun h => (armPullCount b h, armPullCount a h))) := by
      rw [integral_map (hf b a).aemeasurable hg.aestronglyMeasurable]; rfl
    have e2 : ExploreFirst.FundIneq.expPulls νt π T a =
        ∫ p, (p.1 : ℝ) ∂((banditMeasure νt π T).map (fun h => (armPullCount a h, armPullCount b h))) := by
      rw [integral_map (hf a b).aemeasurable hg.aestronglyMeasurable]; rfl
    rw [e1, e2, hmap]
  have hsum := sum_expPulls νt π T
  simp_rw [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hK : (K : ℝ) ≠ 0 := by
    have : 0 < K := Fin.pos a
    exact_mod_cast this.ne'
  field_simp
  linarith
