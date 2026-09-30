-- Prove2me | solution 1 for BanditAlgorithm.bandit_high_probability_lower_bound_at_gap
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:35:29.982669+00:00
-- url     : https://prove2.me/submissions/7d50a660-3475-48f5-94ce-a9a2696bc592

import Definitions.Def_BanditPolicy
import Definitions.Def_GaussianBandit
import Definitions.Def_banditRegret
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 0

/- Complete accepted source by MKPynnic, submission 2cbe6260-7b10-42fb-8a39-bcbc61655b0a. -/
namespace FixedGapDependency0
open _root_.BanditAlgorithm

/-!
Direct-proof work for Lattimore--Szepesvári, Lemma 4.5, printed p. 63:
the canonical reward drawn after selecting arm `i` has conditional mean `μ_i`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem stepKernel_centered_integrable_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ)
    (h : BanditHistory k n) :
    Integrable (fun z : Fin k × ℝ ↦ z.2 - banditArmMean ν z.1)
      (banditStepKernel ν π n h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun i ↦ by
      have hsub : Integrable (fun y : ℝ => y - banditArmMean ν i) (ν.P i) :=
        ((hInt i).sub (integrable_const _)).congr (Filter.Eventually.of_forall fun y => rfl)
      simpa [banditRewardKernel, Kernel.ofFunOfCountable] using hsub
  · exact Integrable.of_finite

theorem stepKernel_integral_centered_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ)
    (h : BanditHistory k n) :
    ∫ z : Fin k × ℝ, (z.2 - banditArmMean ν z.1) ∂(banditStepKernel ν π n h) = 0 := by
  have hz := stepKernel_centered_integrable_test ν hInt π n h
  rw [banditStepKernel] at hz ⊢
  rw [ProbabilityTheory.integral_compProd hz]
  apply integral_eq_zero_of_ae
  filter_upwards [] with i
  change (∫ y : ℝ, y - banditArmMean ν i ∂(ν.P i)) = 0
  have hy : Integrable (fun y : ℝ ↦ y) (ν.P i) := by simpa only [Function.id_def] using hInt i
  rw [integral_sub hy (integrable_const _)]
  simp [banditArmMean]

theorem joint_centered_step_integrable_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        p.2.2 - banditArmMean ν p.2.1)
      ((banditMeasure ν π n).compProd (banditStepKernel ν π n)) := by
  let moment : Fin k → ℝ := fun i ↦ ∫ y, |y - banditArmMean ν i| ∂(ν.P i)
  let C : ℝ := ∑ i, moment i
  apply (Measure.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      stepKernel_centered_integrable_test ν hInt π n h
  · apply Integrable.of_mem_Icc 0 C
    · exact ((by fun_prop : StronglyMeasurable
        (fun p : BanditHistory k n × (Fin k × ℝ) ↦
          |p.2.2 - banditArmMean ν p.2.1|))).integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z ↦ abs_nonneg _)
        · have hz := (stepKernel_centered_integrable_test ν hInt π n h).norm
          have hcond :
              (∫ z : Fin k × ℝ, |z.2 - banditArmMean ν z.1|
                ∂(banditStepKernel ν π n h)) =
              ∫ i : Fin k, moment i ∂(π.select n h) := by
            rw [banditStepKernel] at hz ⊢
            change (∫ z : Fin k × ℝ, ‖z.2 - banditArmMean ν z.1‖
              ∂((π.select n).compProd
                ((banditRewardKernel ν).comap Prod.snd measurable_snd)) h) = _
            rw [ProbabilityTheory.integral_compProd hz]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun i ↦ by rfl
          change (∫ z : Fin k × ℝ, |z.2 - banditArmMean ν z.1|
            ∂(banditStepKernel ν π n h)) ≤ C
          rw [hcond]
          calc
            (∫ i : Fin k, moment i ∂(π.select n h)) ≤
                ∫ _i : Fin k, C ∂(π.select n h) := by
              apply integral_mono_ae Integrable.of_finite (integrable_const _)
              exact Filter.Eventually.of_forall fun i ↦ by
                dsimp [C]
                apply Finset.single_le_sum
                · intro j hj
                  dsimp [moment]
                  exact integral_nonneg_of_ae
                    (Filter.Eventually.of_forall fun y ↦ abs_nonneg _)
                · simp
            _ = C := by simp

theorem expected_centered_sum_zero_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    Integrable (fun h : BanditHistory k n ↦
      ∑ t, ((h t).2 - banditArmMean ν (h t).1)) (banditMeasure ν π n) ∧
    ∫ h, (∑ t, ((h t).2 - banditArmMean ν (h t).1))
      ∂(banditMeasure ν π n) = 0 := by
  let centered : (m : ℕ) → BanditHistory k m → ℝ :=
    fun m h ↦ ∑ t, ((h t).2 - banditArmMean ν (h t).1)
  have centered_measurable : ∀ m : ℕ, Measurable (centered m) := by
    intro m
    dsimp [centered]
    apply Finset.measurable_sum
    intro t ht
    exact (measurable_snd.comp (measurable_pi_apply t)).sub
      ((measurable_of_countable (banditArmMean ν)).comp
        (measurable_fst.comp (measurable_pi_apply t)))
  have hmain : ∀ m : ℕ,
      Integrable (centered m) (banditMeasure ν π m) ∧
        ∫ h, centered m h ∂(banditMeasure ν π m) = 0 := by
    intro m
    induction m with
    | zero => simp [centered]
    | succ m ihm =>
        let μ := banditMeasure ν π m
        let κ := banditStepKernel ν π m
        let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
          fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
        have hsnoc : Measurable snoc := measurable_banditHistorySnoc
        have hrewrite : (fun p ↦ centered (m + 1) (snoc p)) =
            fun p ↦ centered m p.1 + (p.2.2 - banditArmMean ν p.2.1) := by
          funext p
          simp [centered, snoc, Fin.sum_univ_castSucc]
          ring
        have hold : Integrable
            (fun p : BanditHistory k m × (Fin k × ℝ) ↦ centered m p.1)
            (μ.compProd κ) := by
          have hi : Integrable (centered m) (Measure.map Prod.fst (μ.compProd κ)) := by
            change Integrable (centered m) ((μ.compProd κ).fst)
            rw [Measure.fst_compProd]
            exact ihm.1
          exact hi.comp_aemeasurable measurable_fst.aemeasurable
        have hnew : Integrable
            (fun p : BanditHistory k m × (Fin k × ℝ) ↦
              p.2.2 - banditArmMean ν p.2.1) (μ.compProd κ) :=
          joint_centered_step_integrable_test ν hInt π m
        have hsum := hold.add hnew
        have hcomp : Integrable (centered (m + 1) ∘ snoc) (μ.compProd κ) := by
          change Integrable (fun p ↦ centered (m + 1) (snoc p)) (μ.compProd κ)
          rw [hrewrite]
          exact hsum
        constructor
        · rw [banditMeasure]
          apply (integrable_map_measure (centered_measurable (m + 1)).aestronglyMeasurable
            hsnoc.aemeasurable).2
          exact hcomp
        · rw [banditMeasure,
            integral_map hsnoc.aemeasurable (centered_measurable (m + 1)).aestronglyMeasurable]
          change (∫ p, centered (m + 1) (snoc p) ∂(μ.compProd κ)) = 0
          rw [hrewrite]
          rw [integral_add hold hnew]
          rw [Measure.integral_compProd hold, Measure.integral_compProd hnew]
          simp [μ, κ, ihm.2, stepKernel_integral_centered_test ν hInt π m]
  exact hmain n

private theorem pullCount_cast_eq_sum_indicator_test {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by ext t; simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem mean_occupation_pointwise_test {k n : ℕ} (ν : StochasticBandit k)
    (h : BanditHistory k n) :
    ∑ t, banditArmMean ν (h t).1 =
      ∑ i, banditArmMean ν i * (armPullCount i h : ℝ) := by
  simp_rw [pullCount_cast_eq_sum_indicator_test, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp

private theorem integrable_pullCount_test {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · simp_rw [pullCount_cast_eq_sum_indicator_test]
    have hm : Measurable (fun h : BanditHistory k n ↦
        ∑ t : Fin n, if (h t).1 = i then (1 : ℝ) else 0) := by
      apply Finset.measurable_sum
      intro t ht
      have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
        measurable_fst.comp (measurable_pi_apply t)
      exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
        measurable_const measurable_const
    exact hm.aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator_test]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤ ∑ _t : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            split <;> norm_num
          _ = n := by simp

theorem expected_reward_eq_arm_occupation_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n) =
      ∑ i, banditArmMean ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
  classical
  let C : ℝ := ∑ i, |banditArmMean ν i|
  have hmeanTerm : ∀ t : Fin n,
      Integrable (fun h : BanditHistory k n ↦ banditArmMean ν (h t).1)
        (banditMeasure ν π n) := by
    intro t
    apply Integrable.of_mem_Icc (-C) C
    · exact (((measurable_of_countable (banditArmMean ν)).comp
        (measurable_fst.comp (measurable_pi_apply t))).aemeasurable)
    · exact Filter.Eventually.of_forall fun h ↦ by
        have hle : |banditArmMean ν (h t).1| ≤ C := by
          dsimp [C]
          refine Finset.single_le_sum (s := Finset.univ)
            (f := fun i : Fin k ↦ |banditArmMean ν i|) ?_ ?_
          · intro i hi; exact abs_nonneg _
          · exact Finset.mem_univ _
        exact (abs_le.mp hle)
  have hmean : Integrable (fun h : BanditHistory k n ↦
      ∑ t, banditArmMean ν (h t).1) (banditMeasure ν π n) := by
    exact integrable_finset_sum _ fun t ht ↦ hmeanTerm t
  have hc := expected_centered_sum_zero_test ν hInt π n
  have hreward : Integrable (fun h : BanditHistory k n ↦ ∑ t, (h t).2)
      (banditMeasure ν π n) := by
    have hadd := hc.1.add hmean
    apply hadd.congr
    exact Filter.Eventually.of_forall fun h ↦ by
      simp only [Finset.sum_sub_distrib]
      change (∑ t, (h t).2) - (∑ t, banditArmMean ν (h t).1) +
          (∑ t, banditArmMean ν (h t).1) = ∑ t, (h t).2
      ring
  have hreward_mean :
      (∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n)) =
      ∫ h, (∑ t, banditArmMean ν (h t).1) ∂(banditMeasure ν π n) := by
    have hz := hc.2
    simp_rw [Finset.sum_sub_distrib] at hz
    rw [integral_sub hreward hmean] at hz
    exact sub_eq_zero.mp hz
  rw [hreward_mean]
  calc
    (∫ h, (∑ t, banditArmMean ν (h t).1) ∂(banditMeasure ν π n)) =
        ∫ h, (∑ i, banditArmMean ν i * (armPullCount i h : ℝ))
          ∂(banditMeasure ν π n) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun h ↦ mean_occupation_pointwise_test ν h
    _ = ∑ i, banditArmMean ν i *
          ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
            rw [integral_finset_sum]
            · simp_rw [integral_const_mul]
            · intro i hi
              exact (integrable_pullCount_test ν π i).const_mul _

end BanditAlgorithm

theorem checked {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.banditMeasure ν π n) =
      ∑ i, BanditAlgorithm.banditArmMean ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n) := by
  exact BanditAlgorithm.expected_reward_eq_arm_occupation_test ν hInt π n

end FixedGapDependency0

section FixedGapInterface0

open MeasureTheory ProbabilityTheory
namespace BanditAlgorithm

theorem bandit_expected_reward_eq_arm_occupation {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n) =
      ∑ i, banditArmMean ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
  apply FixedGapDependency0.checked <;> assumption

end BanditAlgorithm
end FixedGapInterface0

/- Complete accepted source by MKPynnic, submission ba3eb7f8-b493-4bb3-be82-e5debcf6c729. -/
namespace FixedGapDependency1
open _root_.BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem sum_pullCount_cast {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, (armPullCount i h : ℝ) = n := by
  simp_rw [pullCount_cast_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

private theorem integrable_pullCount {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · simp_rw [pullCount_cast_eq_sum_indicator]
    have hm : Measurable (fun h : BanditHistory k n ↦
        ∑ t : Fin n, if (h t).1 = i then (1 : ℝ) else 0) := by
      apply Finset.measurable_sum
      intro t ht
      have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
        measurable_fst.comp (measurable_pi_apply t)
      exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
        measurable_const measurable_const
    exact hm.aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
              ∑ _t : Fin n, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro t ht
                split <;> norm_num
          _ = n := by simp

end BanditAlgorithm

theorem checked {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    (∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.banditMeasure ν π n) =
      ∑ i, BanditAlgorithm.banditArmMean ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n)) ∧
    (∑ i, ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
      ∂(BanditAlgorithm.banditMeasure ν π n)) = n := by
  classical
  constructor
  · exact BanditAlgorithm.bandit_expected_reward_eq_arm_occupation ν hInt π n
  · rw [← integral_finset_sum]
    · calc
        ∫ h, (∑ i, (BanditAlgorithm.armPullCount i h : ℝ))
              ∂(BanditAlgorithm.banditMeasure ν π n) =
            ∫ _h, (n : ℝ) ∂(BanditAlgorithm.banditMeasure ν π n) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun h ↦
                BanditAlgorithm.sum_pullCount_cast h
        _ = n := by simp
    · intro i hi
      exact BanditAlgorithm.integrable_pullCount ν π i

end FixedGapDependency1

section FixedGapInterface1

open MeasureTheory ProbabilityTheory
namespace BanditAlgorithm

theorem bandit_canonical_occupation_identities {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    (∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n) =
      ∑ i, banditArmMean ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n)) ∧
    (∑ i, ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n)) = n := by
  apply FixedGapDependency1.checked <;> assumption

end BanditAlgorithm
end FixedGapInterface1

/- Complete accepted source by MKPynnic, submission bf91687c-e018-48a5-9321-7058d5893bc1. -/
namespace FixedGapDependency2
open _root_.BanditAlgorithm

/-!
Source-faithful reduction of Lattimore and Szepesvári, *Bandit Algorithms*
(CUP 2020), Lemma 4.5, printed pp. 62--63.  The imported child isolates the
conditional-reward and occupation-count identities proved around Eq. (4.6).
This file performs the remaining gap-weighted finite-sum algebra.
-/

open MeasureTheory ProbabilityTheory

theorem checked {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    BanditAlgorithm.banditRegret ν π n =
      ∑ i, BanditAlgorithm.banditGap ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n) := by
  classical
  rcases BanditAlgorithm.bandit_canonical_occupation_identities ν hInt π n with
    ⟨hreward, hcount⟩
  rw [BanditAlgorithm.banditRegret, hreward]
  simp_rw [BanditAlgorithm.banditGap, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
  ring

end FixedGapDependency2

section FixedGapInterface2


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_regret_decomposition {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    banditRegret ν π n =
      ∑ i, banditGap ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
  apply FixedGapDependency2.checked <;> assumption

end FixedGapInterface2

/- Complete accepted source by Harry_Xu, submission e5c3f2ab-e884-4afd-a4ab-94e92ac25ff4. -/
namespace FixedGapDependency3
open _root_.BanditAlgorithm

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Lemma 15.1 and Eq. (15.2),
printed pp. 198--199 / PDF pp. 207--208.

This slot81 scratch isolates the exact conditional one-round computation in
the divergence decomposition: after conditioning on the selected arm, the
KL divergence is the policy-weighted sum of the arm divergences.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace Slot81DivergenceStepScratch

open BanditAlgorithm

private theorem arm_ac {k : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤) (i : Fin k) :
    nu.P i ≪ nu'.P i :=
  (klDiv_ne_top_iff.mp (hKL i)).1

private theorem measurable_arm_rnDeriv {k : ℕ} (nu nu' : StochasticBandit k) :
    Measurable (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  classical
  let f : Fin k × ℝ → ENNReal := fun z ↦
    ∑ i, Set.indicator {z : Fin k × ℝ | z.1 = i}
      (fun z ↦ (nu.P i).rnDeriv (nu'.P i) z.2) z
  have hf : Measurable f := by
    dsimp [f]
    apply Finset.measurable_sum
    intro i _
    exact ((Measure.measurable_rnDeriv (nu.P i) (nu'.P i)).comp measurable_snd).indicator
      ((measurableSet_singleton i).preimage measurable_fst)
  have h_eq : f = fun z : Fin k × ℝ ↦
      (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
    funext z
    simp only [f, Set.indicator_apply, Set.mem_setOf_eq]
    rw [Finset.sum_ite_eq]
    simp
  rwa [← h_eq]

private theorem step_ac {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    banditStepKernel nu pi n h ≪ banditStepKernel nu' pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [] with i
  simpa [Kernel.sectR_apply, banditRewardKernel, Kernel.ofFunOfCountable] using arm_ac nu nu' hKL i

private theorem step_withDensity {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    (banditStepKernel nu' pi n h).withDensity
        (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) =
      banditStepKernel nu pi n h := by
  rw [banditStepKernel, banditStepKernel]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR]
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_arm_rnDeriv nu nu').indicator hs)]
  apply lintegral_congr
  intro i
  rw [Kernel.sectR_apply, Kernel.sectR_apply]
  simp only [Kernel.comap_apply, banditRewardKernel]
  change (∫⁻ x, s.indicator
      (fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2) (i, x)
      ∂nu'.P i) = nu.P i (Prod.mk i ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk i ⁻¹' s,
        (nu.P i).rnDeriv (nu'.P i) x ∂nu'.P i := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = nu.P i (Prod.mk i ⁻¹' s) :=
      Measure.setLIntegral_rnDeriv (arm_ac nu nu' hKL i) _

private theorem rnDeriv_step {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    (banditStepKernel nu pi n h).rnDeriv (banditStepKernel nu' pi n h) =ᵐ[
      banditStepKernel nu' pi n h]
        fun z : Fin k × ℝ ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2 := by
  rw [← step_withDensity nu nu' hKL pi h]
  exact Measure.rnDeriv_withDensity _ (measurable_arm_rnDeriv nu nu')

private theorem klDiv_banditStepKernel_eq_sum {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) (h : BanditHistory k n) :
    klDiv (banditStepKernel nu pi n h) (banditStepKernel nu' pi n h) =
      ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' hKL pi h)]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun (((banditStepKernel nu pi n h).rnDeriv
          (banditStepKernel nu' pi n h)) z).toReal)
        ∂banditStepKernel nu' pi n h) =
        ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' hKL pi h] with z hz
      rw [hz]
    _ = ∫⁻ i, klDiv (nu.P i) (nu'.P i) ∂pi.select n h := by
      rw [banditStepKernel]
      rw [Kernel.compProd_apply_eq_compProd_sectR]
      have hmeas : Measurable (fun z : Fin k × ℝ ↦ ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp (measurable_arm_rnDeriv nu nu')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr
      intro i
      rw [Kernel.sectR_apply]
      simp only [Kernel.comap_apply, banditRewardKernel]
      change (∫⁻ x, ENNReal.ofReal
          (klFun (((nu.P i).rnDeriv (nu'.P i) x).toReal)) ∂nu'.P i) = _
      rw [klDiv_eq_lintegral_klFun_of_ac (arm_ac nu nu' hKL i)]
    _ = ∑ i, klDiv (nu.P i) (nu'.P i) * (pi.select n h) {i} := by
      exact lintegral_fintype _
    _ = ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [ofReal_measureReal, mul_comm]

private theorem stepKernel_eq_withDensity {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    banditStepKernel nu pi n =
      (banditStepKernel nu' pi n).withDensity
        (fun (_ : BanditHistory k n) (z : Fin k × ℝ) ↦
          (nu.P z.1).rnDeriv (nu'.P z.1) z.2) := by
  have hf : Measurable (Function.uncurry
      (fun (_ : BanditHistory k n) (z : Fin k × ℝ) ↦
        (nu.P z.1).rnDeriv (nu'.P z.1) z.2)) :=
    (measurable_arm_rnDeriv nu nu').comp measurable_snd
  ext h s hs
  rw [Kernel.withDensity_apply _ hf h]
  exact congrArg (fun m : Measure (Fin k × ℝ) ↦ m s)
    (step_withDensity nu nu' hKL pi h).symm

private theorem banditCompProd_withDensity {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)).withDensity
        (fun p ↦ (nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2) =
      (banditMeasure nu pi n).compProd (banditStepKernel nu pi n) := by
  let f : BanditHistory k n → Fin k × ℝ → ENNReal :=
    fun _ z ↦ (nu.P z.1).rnDeriv (nu'.P z.1) z.2
  have hf : Measurable (Function.uncurry f) :=
    (measurable_arm_rnDeriv nu nu').comp measurable_snd
  have hstep : banditStepKernel nu pi n =
      (banditStepKernel nu' pi n).withDensity f := by
    simpa [f] using stepKernel_eq_withDensity nu nu' hKL pi
  letI : IsFiniteKernel ((banditStepKernel nu' pi n).withDensity f) := by
    rw [← hstep]
    infer_instance
  change ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)).withDensity
      (fun p ↦ f p.1 p.2) =
    (banditMeasure nu pi n).compProd (banditStepKernel nu pi n)
  rw [← Measure.compProd_withDensity hf]
  rw [← hstep]

private theorem rnDeriv_banditCompProd {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n)).rnDeriv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =ᵐ[
      (banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)]
        fun p ↦ (nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2 := by
  rw [← banditCompProd_withDensity nu nu' hKL pi]
  exact Measure.rnDeriv_withDensity _
    ((measurable_arm_rnDeriv nu nu').comp measurable_snd)

private theorem banditCompProd_ac {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    (banditMeasure nu pi n).compProd (banditStepKernel nu pi n) ≪
      (banditMeasure nu pi n).compProd (banditStepKernel nu' pi n) := by
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  filter_upwards [] with h
  exact step_ac nu nu' hKL pi h

private theorem klDiv_banditCompProd_eq_lintegral_step {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
      ∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n := by
  rw [klDiv_eq_lintegral_klFun_of_ac (banditCompProd_ac nu nu' hKL pi)]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun ((((banditMeasure nu pi n).compProd (banditStepKernel nu pi n)).rnDeriv
          ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) p).toReal))
        ∂(banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
        ∫⁻ p, ENNReal.ofReal
          (klFun (((nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2).toReal))
          ∂(banditMeasure nu pi n).compProd (banditStepKernel nu' pi n) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_banditCompProd nu nu' hKL pi] with p hp
      rw [hp]
    _ = ∫⁻ h, ∫⁻ z, ENNReal.ofReal
          (klFun (((nu.P z.1).rnDeriv (nu'.P z.1) z.2).toReal))
          ∂banditStepKernel nu' pi n h ∂banditMeasure nu pi n := by
      have hmeas : Measurable (fun p : BanditHistory k n × (Fin k × ℝ) ↦
          ENNReal.ofReal
            (klFun (((nu.P p.2.1).rnDeriv (nu'.P p.2.1) p.2.2).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp
              ((measurable_arm_rnDeriv nu nu').comp measurable_snd)))
      rw [Measure.lintegral_compProd hmeas]
    _ = ∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n := by
      apply lintegral_congr
      intro h
      rw [klDiv_eq_lintegral_klFun_of_ac (step_ac nu nu' hKL pi h)]
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_step nu nu' hKL pi h] with z hz
      rw [hz]

private theorem measurable_selection_probability {k n : ℕ}
    (pi : BanditPolicy k) (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (pi.select n h).real {i}) :=
  (Kernel.measurable_coe (pi.select n) (measurableSet_singleton i)).ennreal_toReal

private theorem integrable_selection_probability {k n : ℕ}
    (nu : StochasticBandit k) (pi : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (pi.select n h).real {i})
      (banditMeasure nu pi n) := by
  apply Integrable.of_mem_Icc 0 1
  · exact (measurable_selection_probability pi i).aemeasurable
  · filter_upwards [] with h
    constructor
    · positivity
    · calc
        (pi.select n h).real {i} ≤ (pi.select n h).real Set.univ :=
          measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp

private theorem klDiv_banditCompProd_eq_sum_selection_integrals {k n : ℕ}
    (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv
        ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
        ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) =
      ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
        klDiv (nu.P i) (nu'.P i) := by
  rw [klDiv_banditCompProd_eq_lintegral_step nu nu' hKL pi]
  calc
    (∫⁻ h, klDiv (banditStepKernel nu pi n h)
        (banditStepKernel nu' pi n h) ∂banditMeasure nu pi n) =
        ∫⁻ h, ∑ i, ENNReal.ofReal ((pi.select n h).real {i}) *
          klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n := by
      apply lintegral_congr
      intro h
      exact klDiv_banditStepKernel_eq_sum nu nu' hKL pi h
    _ = ∑ i, ∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i}) *
          klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n := by
      rw [lintegral_finset_sum]
      intro i _
      exact (ENNReal.measurable_ofReal.comp
        (measurable_selection_probability pi i)).mul_const _
    _ = ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
        klDiv (nu.P i) (nu'.P i) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i}) *
            klDiv (nu.P i) (nu'.P i) ∂banditMeasure nu pi n) =
            (∫⁻ h, ENNReal.ofReal ((pi.select n h).real {i})
              ∂banditMeasure nu pi n) * klDiv (nu.P i) (nu'.P i) :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
            (measurable_selection_probability pi i))
        _ = ENNReal.ofReal
            (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
              klDiv (nu.P i) (nu'.P i) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            (integrable_selection_probability nu pi i)]
          filter_upwards [] with h
          positivity

private theorem klDiv_map_embedding
    {alpha beta : Type*} {ma : MeasurableSpace alpha} {mb : MeasurableSpace beta}
    {mu eta : Measure alpha} [IsFiniteMeasure mu] [IsFiniteMeasure eta]
    {f : alpha → beta} (hf : MeasurableEmbedding f) :
    klDiv (mu.map f) (eta.map f) = klDiv mu eta := by
  by_cases h_ac : mu ≪ eta
  · rw [klDiv_eq_lintegral_klFun_of_ac (hf.absolutelyContinuous_map h_ac),
      klDiv_eq_lintegral_klFun_of_ac h_ac]
    rw [hf.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map mu eta] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
    intro hmap
    apply h_ac
    intro s hetas
    have hetamap : eta.map f (f '' s) = 0 := by
      rw [hf.map_apply, hf.injective.preimage_image]
      exact hetas
    have hmumap := hmap hetamap
    rw [hf.map_apply, hf.injective.preimage_image] at hmumap
    exact hmumap

private theorem klDiv_banditSnoc_map {k n : ℕ}
    (mu eta : Measure (BanditHistory k n × (Fin k × ℝ)))
    [IsFiniteMeasure mu] [IsFiniteMeasure eta] :
    klDiv
        (mu.map (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2))
        (eta.map (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2)) =
      klDiv mu eta := by
  have hemb : MeasurableEmbedding
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) := by
    apply MeasurableEmbedding.of_measurable_inverse
      (g := fun h : BanditHistory k (n + 1) ↦ (Fin.init h, h (Fin.last n)))
      measurable_banditHistorySnoc
    · have hrange : Set.range
          (fun p : BanditHistory k n × (Fin k × ℝ) ↦
            Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro h
        exact ⟨(Fin.init h, h (Fin.last n)), Fin.snoc_init_self (q := h)⟩
      rw [hrange]
      exact MeasurableSet.univ
    · fun_prop
    · intro p
      apply Prod.ext
      · exact Fin.init_snoc
          (α := fun _ : Fin (n + 1) ↦ Fin k × ℝ) (n := n) (p := p.1) (x := p.2)
      · exact Fin.snoc_last
          (α := fun _ : Fin (n + 1) ↦ Fin k × ℝ) (n := n) (p := p.1) (x := p.2)
  exact klDiv_map_embedding hemb

private theorem klDiv_banditMeasure_succ_chainRule {k n : ℕ}
    (nu nu' : StochasticBandit k) (pi : BanditPolicy k) :
    klDiv (banditMeasure nu pi (n + 1)) (banditMeasure nu' pi (n + 1)) =
      klDiv (banditMeasure nu pi n) (banditMeasure nu' pi n) +
        klDiv
          ((banditMeasure nu pi n).compProd (banditStepKernel nu pi n))
          ((banditMeasure nu pi n).compProd (banditStepKernel nu' pi n)) := by
  rw [banditMeasure, banditMeasure]
  rw [klDiv_banditSnoc_map]
  exact InformationTheory.klDiv_compProd_eq_add _ _ _ _

end Slot81DivergenceStepScratch

open MeasureTheory ProbabilityTheory InformationTheory
open BanditAlgorithm

theorem checked {k n : ℕ} (nu nu' : StochasticBandit k)
    (hKL : ∀ i, klDiv (nu.P i) (nu'.P i) ≠ ⊤)
    (pi : BanditPolicy k) :
    klDiv (banditMeasure nu pi (n + 1)) (banditMeasure nu' pi (n + 1)) =
      klDiv (banditMeasure nu pi n) (banditMeasure nu' pi n) +
        ∑ i, ENNReal.ofReal
          (∫ h, (pi.select n h).real {i} ∂banditMeasure nu pi n) *
            klDiv (nu.P i) (nu'.P i) := by
  rw [Slot81DivergenceStepScratch.klDiv_banditMeasure_succ_chainRule]
  congr 1
  exact Slot81DivergenceStepScratch.klDiv_banditCompProd_eq_sum_selection_integrals
    nu nu' hKL pi

end FixedGapDependency3

section FixedGapInterface3

open MeasureTheory ProbabilityTheory InformationTheory
theorem BanditAlgorithm.bandit_divergence_one_step {k n : ℕ} (ν ν' : StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditPolicy k) :
    klDiv (banditMeasure ν π (n + 1)) (banditMeasure ν' π (n + 1)) =
      klDiv (banditMeasure ν π n) (banditMeasure ν' π n) +
        ∑ i, ENNReal.ofReal
          (∫ h, (π.select n h).real {i} ∂banditMeasure ν π n) *
            klDiv (ν.P i) (ν'.P i) := by
  apply FixedGapDependency3.checked <;> assumption
end FixedGapInterface3

/- Complete accepted source by Harry_Xu, submission 93936f39-b9b6-444b-b16f-446adfd079fe. -/
namespace FixedGapDependency4
open _root_.BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 15.1 and Eq. (15.1),
printed p. 198 / PDF p. 207.

The imported one-step identity is Eq. (15.2).  This file proves the formal
bridge from that identity to the full horizon decomposition by establishing
the one-step recurrence for expected arm occupation counts and then inducting
on the horizon.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
      Finset.univ).symm

private theorem measurable_pullCount_cast {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem integrable_pullCount {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_pullCount_cast i).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
              ∑ _t : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            split <;> norm_num
          _ = n := by simp

private theorem pullCount_cast_snoc {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ) =
      (armPullCount i h : ℝ) + if z.1 = i then 1 else 0 := by
  calc
    (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) : ℝ) =
        ∑ t : Fin (n + 1),
          if ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) t).1 = i
          then 1 else 0 :=
      pullCount_cast_eq_sum_indicator i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)
    _ = (∑ t : Fin n, if (h t).1 = i then 1 else 0) +
          if z.1 = i then 1 else 0 := by
      rw [Fin.sum_univ_castSucc]
      simp
    _ = (armPullCount i h : ℝ) + if z.1 = i then 1 else 0 := by
      rw [pullCount_cast_eq_sum_indicator]

private theorem integrable_step_arm_indicator {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k)
    (h : BanditHistory k n) :
    Integrable (fun z : Fin k × ℝ ↦ if z.1 = i then (1 : ℝ) else 0)
      (banditStepKernel ν π n h) := by
  apply Integrable.of_mem_Icc 0 1
  · exact
      (Measurable.ite
        ((measurableSet_singleton i).preimage measurable_fst)
        measurable_const measurable_const).aemeasurable
  · exact Filter.Eventually.of_forall fun z ↦ by
      split <;> norm_num

private theorem stepKernel_integral_arm_indicator {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k)
    (h : BanditHistory k n) :
    ∫ z : Fin k × ℝ, (if z.1 = i then (1 : ℝ) else 0)
        ∂(banditStepKernel ν π n h) =
      (π.select n h).real {i} := by
  have hz := integrable_step_arm_indicator ν π i h
  rw [banditStepKernel] at hz ⊢
  rw [ProbabilityTheory.integral_compProd hz]
  calc
    (∫ x : Fin k, ∫ y : ℝ, (if x = i then (1 : ℝ) else 0)
        ∂(banditRewardKernel ν) x ∂(π.select n) h) =
        ∫ x : Fin k, (if x = i then (1 : ℝ) else 0)
          ∂(π.select n) h := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hxi : x = i <;> simp [hxi]
    _ = ((π.select n) h).real {i} := by
      simpa only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] using
        (integral_indicator_one (μ := (π.select n) h)
          (measurableSet_singleton i))

private theorem expected_pullCount_succ {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π (n + 1) =
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) +
        ∫ h, (π.select n h).real {i} ∂banditMeasure ν π n := by
  let μ := banditMeasure ν π n
  let κ := banditStepKernel ν π n
  let snoc : BanditHistory k n × (Fin k × ℝ) →
      BanditHistory k (n + 1) :=
    fun p ↦ Fin.snoc p.1 p.2
  have hsnoc : Measurable snoc := measurable_banditHistorySnoc
  have hrewrite :
      (fun p ↦ (armPullCount i (snoc p) : ℝ)) =
        fun p ↦ (armPullCount i p.1 : ℝ) +
          if p.2.1 = i then 1 else 0 := by
    funext p
    exact pullCount_cast_snoc i p.1 p.2
  have hold : Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) (μ.compProd κ) := by
    have hi : Integrable
        (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
        (Measure.map Prod.fst (μ.compProd κ)) := by
      change Integrable
        (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
        ((μ.compProd κ).fst)
      rw [Measure.fst_compProd]
      exact integrable_pullCount ν π i
    exact hi.comp_aemeasurable measurable_fst.aemeasurable
  have hnew : Integrable
      (fun p : BanditHistory k n × (Fin k × ℝ) ↦
        if p.2.1 = i then (1 : ℝ) else 0) (μ.compProd κ) := by
    apply Integrable.of_mem_Icc 0 1
    · exact
        (Measurable.ite
          ((measurableSet_singleton i).preimage
            (measurable_fst.comp measurable_snd))
          measurable_const measurable_const).aemeasurable
    · exact Filter.Eventually.of_forall fun p ↦ by
        split <;> norm_num
  rw [banditMeasure,
    integral_map hsnoc.aemeasurable
      (measurable_pullCount_cast i).aestronglyMeasurable]
  change (∫ p, (armPullCount i (snoc p) : ℝ) ∂(μ.compProd κ)) = _
  rw [hrewrite, integral_add hold hnew]
  rw [Measure.integral_compProd hold, Measure.integral_compProd hnew]
  congr 1
  · simp [μ, κ]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h ↦
      stepKernel_integral_arm_indicator ν π i h

private theorem expected_pullCount_nonneg {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    0 ≤ ∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n :=
  integral_nonneg fun h ↦ by positivity

private theorem expected_selection_nonneg {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    0 ≤ ∫ h, (π.select n h).real {i} ∂banditMeasure ν π n :=
  integral_nonneg fun h ↦ by positivity

end BanditAlgorithm

theorem checked {k : ℕ}
    (ν ν' : BanditAlgorithm.StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditAlgorithm.BanditPolicy k) (n : ℕ) :
    klDiv (BanditAlgorithm.banditMeasure ν π n)
        (BanditAlgorithm.banditMeasure ν' π n) =
      ∑ i, ENNReal.ofReal
          (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
            ∂BanditAlgorithm.banditMeasure ν π n) *
        klDiv (ν.P i) (ν'.P i) := by
  classical
  induction n with
  | zero =>
      simp [BanditAlgorithm.banditMeasure, BanditAlgorithm.armPullCount]
  | succ n ih =>
      rw [BanditAlgorithm.bandit_divergence_one_step ν ν' hKL π, ih]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [BanditAlgorithm.expected_pullCount_succ]
      rw [ENNReal.ofReal_add
        (BanditAlgorithm.expected_pullCount_nonneg ν π i)
        (BanditAlgorithm.expected_selection_nonneg ν π i)]
      rw [add_mul]

end FixedGapDependency4

section FixedGapInterface4


open MeasureTheory ProbabilityTheory InformationTheory

theorem BanditAlgorithm.bandit_divergence_decomposition {k : ℕ} (ν ν' : StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditPolicy k) (n : ℕ) :
    klDiv (banditMeasure ν π n) (banditMeasure ν' π n) =
      ∑ i, ENNReal.ofReal (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) *
        klDiv (ν.P i) (ν'.P i) := by
  apply FixedGapDependency4.checked <;> assumption

end FixedGapInterface4

/- Complete accepted source by Harry_Xu, submission 1ce752fa-2d67-4191-9052-1cd80d4cf9f2. -/
namespace FixedGapDependency5
open _root_.BanditAlgorithm

open MeasureTheory ProbabilityTheory InformationTheory NNReal

/-!
Source: Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020), Section 14.2,
printed p. 189 (PDF p. 198), immediately after Eq. (14.6). For Gaussian
probability measures with means `mu1`, `mu2` and common positive variance `v`,
the log-density ratio is affine in the sample. Integrating it under the first
Gaussian leaves `(mu1 - mu2)^2 / (2 * v)`.
-/

theorem checked (mu1 mu2 : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal mu1 v) (gaussianReal mu2 v) =
      ENNReal.ofReal ((mu1 - mu2) ^ 2 / (2 * (v : ℝ))) := by
  let P := gaussianReal mu1 v
  let Q := gaussianReal mu2 v
  have hPvol : P ≪ volume := gaussianReal_absolutelyContinuous mu1 hv
  have hvolQ : volume ≪ Q := gaussianReal_absolutelyContinuous' mu2 hv
  have hPQ : P ≪ Q := hPvol.trans hvolQ
  have hQvol : Q ≪ volume := gaussianReal_absolutelyContinuous mu2 hv
  have hratio :
      P.rnDeriv Q =ᵐ[Q] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x := by
    filter_upwards [Measure.rnDeriv_eq_div hPvol hQvol,
      hQvol (rnDeriv_gaussianReal mu1 v), hQvol (rnDeriv_gaussianReal mu2 v)]
      with x hx h1 h2
    rw [hx, h1, h2]
  have hratioP :
      P.rnDeriv Q =ᵐ[P] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x :=
    hPQ hratio
  have hllr : llr P Q =ᵐ[P] fun x =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) := by
    filter_upwards [hratioP] with x hx
    rw [llr, hx]
    simp only [ENNReal.toReal_div, toReal_gaussianPDF]
    rw [gaussianPDFReal, gaussianPDFReal]
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by
      positivity
    rw [mul_div_mul_left _ _ hc, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    field_simp
    ring
  have hid : Integrable (fun x : ℝ => x) P := by
    simpa [P, Function.id_def] using (memLp_id_gaussianReal (μ := mu1) (v := v) 1).integrable (by simp)
  have haff : Integrable (fun x : ℝ =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ))) P := by
    have hlin : Integrable (fun x : ℝ =>
        (2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2)) / (2 * (v : ℝ))) P :=
      ((hid.const_mul (2 * (mu1 - mu2))).add (integrable_const _)).div_const _
    exact hlin.congr (ae_of_all _ fun x => by ring)
  have hllr_int : Integrable (llr P Q) P := haff.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hPQ hllr_int]
  congr 1
  simp only [P, Q, probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  calc
    (∫ x, ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) ∂P) =
        (2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2)) /
          (2 * (v : ℝ)) := by
            rw [integral_div]
            congr 1
            calc
              (∫ x, (x - mu2) ^ 2 - (x - mu1) ^ 2 ∂P) =
                  ∫ x, 2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all _ fun x => by ring
              _ = 2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2) := by
                    rw [integral_add (hid.const_mul _) (integrable_const _),
                      integral_const_mul, integral_const]
                    simp
    _ = (mu1 - mu2) ^ 2 / (2 * (v : ℝ)) := by
          simp [P, integral_id_gaussianReal]
          ring

end FixedGapDependency5

section FixedGapInterface5


open MeasureTheory ProbabilityTheory InformationTheory NNReal

theorem BanditAlgorithm.gaussian_relative_entropy_formula (μ₁ μ₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
      ENNReal.ofReal ((μ₁ - μ₂) ^ 2 / (2 * (v : ℝ))) := by
  apply FixedGapDependency5.checked <;> assumption

end FixedGapInterface5

/- Complete accepted source by jianglsbz, submission 4c3f9111-3b2f-43f1-9194-fc711e708456. -/
namespace FixedGapDependency6
open _root_.BanditAlgorithm

open MeasureTheory InformationTheory
open scoped ENNReal

theorem checked {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (2⁻¹ * Real.exp (-(klDiv P Q).toReal)) ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  let ν := P + Q
  let p := fun ω ↦ P.rnDeriv ν ω
  let q := fun ω ↦ Q.rnDeriv ν ω
  let affinity := ∫⁻ ω, min (p ω) (q ω) ∂ν
  let hellingerProduct := ∫⁻ ω, (p ω * q ω) ^ (1 / 2 : ℝ) ∂ν
  let hellingerMinMax := ∫⁻ ω, (min (p ω) (q ω)) ^ (1 / 2 : ℝ) *
    (max (p ω) (q ω)) ^ (1 / 2 : ℝ) ∂ν
  have density_half_identity (a b : ℝ≥0∞) (ha_top : a ≠ ∞)
      (hb_pos : b ≠ 0) (hb_top : b ≠ ∞) :
      a.toReal * Real.exp (-Real.log ((a / b).toReal) / 2) =
        ((a * b) ^ (1 / 2 : ℝ)).toReal := by
    by_cases ha : a = 0
    · simp [ha]
    have haR : 0 < a.toReal := ENNReal.toReal_pos ha ha_top
    have hbR : 0 < b.toReal := ENNReal.toReal_pos hb_pos hb_top
    rw [ENNReal.toReal_div, ← ENNReal.toReal_rpow, ENNReal.toReal_mul]
    rw [Real.exp_half, Real.exp_neg, Real.exp_log (div_pos haR hbR)]
    rw [inv_div, Real.sqrt_div (le_of_lt hbR), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (le_of_lt haR)]
    field_simp [Real.sqrt_ne_zero'.mpr haR, Real.sqrt_ne_zero'.mpr hbR]
    nlinarith [Real.sq_sqrt haR.le, Real.sq_sqrt hbR.le]
  have hJ : Real.exp (-(klDiv P Q).toReal / 2) ≤
      ∫ ω, Real.exp (-llr P Q ω / 2) ∂P := by
    have hD' := klDiv_ne_top_iff.mp hD
    have hPQ : P ≪ Q := hD'.1
    have hllr : Integrable (llr P Q) P := hD'.2
    have hDreal : (klDiv P Q).toReal = ∫ ω, llr P Q ω ∂P := by
      simpa using toReal_klDiv hPQ hllr
    have hrn : Integrable (fun ω ↦ (Q.rnDeriv P ω).toReal) P :=
      Measure.integrable_toReal_rnDeriv
    have hsqrt : Integrable (fun ω ↦ Real.sqrt (Q.rnDeriv P ω).toReal) P := by
      apply integrable_of_le_of_le
        ((Measure.measurable_rnDeriv Q P).ennreal_toReal.sqrt.aestronglyMeasurable)
        (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _) (ae_of_all _ fun ω ↦ ?_)
        (integrable_zero _ _ _) ((integrable_const (1 : ℝ)).add hrn)
      change Real.sqrt (Q.rnDeriv P ω).toReal ≤ 1 + (Q.rnDeriv P ω).toReal
      have hsq := Real.sq_sqrt
        (ENNReal.toReal_nonneg : 0 ≤ (Q.rnDeriv P ω).toReal)
      have hsnonneg := Real.sqrt_nonneg (Q.rnDeriv P ω).toReal
      have hrnonneg :=
        (ENNReal.toReal_nonneg : 0 ≤ (Q.rnDeriv P ω).toReal)
      nlinarith [sq_nonneg (Real.sqrt (Q.rnDeriv P ω).toReal - 1)]
    have hexp_sqrt :
        (fun ω ↦ Real.exp (-llr P Q ω / 2)) =ᵐ[P]
          fun ω ↦ Real.sqrt (Q.rnDeriv P ω).toReal := by
      filter_upwards [exp_neg_llr hPQ] with ω hω
      rw [Real.exp_half, hω]
    have hexp : Integrable (fun ω ↦ Real.exp (-llr P Q ω / 2)) P :=
      (integrable_congr hexp_sqrt).mpr hsqrt
    have hjensen := convexOn_exp.map_integral_le Real.continuousOn_exp isClosed_univ
      (ae_of_all _ fun _ ↦ Set.mem_univ _) (hllr.neg.div_const 2) hexp
    rw [integral_div] at hjensen
    have hnegint : (∫ a, (-llr P Q) a ∂P) = -(∫ a, llr P Q a ∂P) := by
      simpa only [Pi.neg_apply] using integral_neg (μ := P) (f := llr P Q)
    rw [hnegint] at hjensen
    simpa only [Function.comp_apply, Pi.neg_apply, integral_div, hDreal] using hjensen
  have hbridge : (∫ ω, Real.exp (-llr P Q ω / 2) ∂P) =
      hellingerProduct.toReal := by
    have hD' := klDiv_ne_top_iff.mp hD
    have hPQ : P ≪ Q := hD'.1
    have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
    have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
    have hνQ : ν ≪ Q := hPQ.add_left Measure.AbsolutelyContinuous.rfl
    have hratioQ : P.rnDeriv Q =ᵐ[Q] fun ω ↦ p ω / q ω :=
      Measure.rnDeriv_eq_div hPν hQν
    have hratio : P.rnDeriv Q =ᵐ[ν] fun ω ↦ p ω / q ω := hνQ hratioQ
    have hp_top : ∀ᵐ ω ∂ν, p ω ≠ ∞ :=
      (Measure.rnDeriv_lt_top P ν).mono fun _ h ↦ h.ne
    have hq_top : ∀ᵐ ω ∂ν, q ω ≠ ∞ :=
      (Measure.rnDeriv_lt_top Q ν).mono fun _ h ↦ h.ne
    have hq_pos_Q : ∀ᵐ ω ∂Q, 0 < q ω := Measure.rnDeriv_pos hQν
    have hq_pos : ∀ᵐ ω ∂ν, 0 < q ω := hνQ hq_pos_Q
    have heq :
        (fun ω ↦ (p ω).toReal * Real.exp (-llr P Q ω / 2)) =ᵐ[ν]
          fun ω ↦ ((p ω * q ω) ^ (1 / 2 : ℝ)).toReal := by
      filter_upwards [hratio, hp_top, hq_top, hq_pos] with ω hratio hp_top hq_top hq_pos
      simpa only [llr, hratio] using
        density_half_identity (p ω) (q ω) hp_top hq_pos.ne' hq_top
    have hmeas : AEMeasurable (fun ω ↦ (p ω * q ω) ^ (1 / 2 : ℝ)) ν := by
      fun_prop
    have hfinite : ∀ᵐ ω ∂ν, (p ω * q ω) ^ (1 / 2 : ℝ) < ∞ := by
      filter_upwards [hp_top, hq_top] with ω hp_top hq_top
      exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_ne_top hp_top hq_top)
    calc
      ∫ ω, Real.exp (-llr P Q ω / 2) ∂P =
          ∫ ω, (p ω).toReal * Real.exp (-llr P Q ω / 2) ∂ν := by
        symm
        exact integral_toReal_rnDeriv_mul hPν
      _ = ∫ ω, ((p ω * q ω) ^ (1 / 2 : ℝ)).toReal ∂ν :=
        integral_congr_ae heq
      _ = hellingerProduct.toReal := by
        rw [integral_toReal hmeas hfinite]
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have ha_one : affinity ≤ 1 := by
    calc
      affinity ≤ ∫⁻ ω, p ω ∂ν := lintegral_mono fun ω ↦ min_le_left _ _
      _ = P Set.univ := Measure.lintegral_rnDeriv hPν
      _ = 1 := by norm_num
  have ha_top : affinity ≠ ∞ := (lt_of_le_of_lt ha_one ENNReal.one_lt_top).ne
  have hhellinger : hellingerProduct = hellingerMinMax := by
    apply lintegral_congr
    intro ω
    calc
      (p ω * q ω) ^ (1 / 2 : ℝ) =
          (min (p ω) (q ω) * max (p ω) (q ω)) ^ (1 / 2 : ℝ) := by
        rw [min_mul_max]
      _ = (min (p ω) (q ω)) ^ (1 / 2 : ℝ) *
          (max (p ω) (q ω)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        positivity
  have hC : hellingerMinMax ^ (2 : ℝ) ≤ 2 * affinity := by
    let opposite := ∫⁻ ω, max (p ω) (q ω) ∂ν
    have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
    have hp : AEMeasurable p ν := (Measure.measurable_rnDeriv _ _).aemeasurable
    have hq : AEMeasurable q ν := (Measure.measurable_rnDeriv _ _).aemeasurable
    have hmin : AEMeasurable (fun ω ↦ min (p ω) (q ω)) ν := hp.min hq
    have hmax : AEMeasurable (fun ω ↦ max (p ω) (q ω)) ν := hp.max hq
    have hsum : affinity + opposite = 2 := by
      calc
        affinity + opposite = ∫⁻ ω, min (p ω) (q ω) + max (p ω) (q ω) ∂ν := by
          rw [lintegral_add_left' hmin]
        _ = ∫⁻ ω, p ω + q ω ∂ν := by
          apply lintegral_congr
          intro ω
          exact min_add_max (p ω) (q ω)
        _ = (∫⁻ ω, p ω ∂ν) + ∫⁻ ω, q ω ∂ν := lintegral_add_left' hp _
        _ = P Set.univ + Q Set.univ := by
          rw [Measure.lintegral_rnDeriv hPν, Measure.lintegral_rnDeriv hQν]
        _ = 2 := by norm_num
    have hopposite : opposite ≤ 2 := by
      calc
        opposite ≤ affinity + opposite := le_add_left le_rfl
        _ = 2 := hsum
    have hholder : hellingerMinMax ≤
        affinity ^ (1 / 2 : ℝ) * opposite ^ (1 / 2 : ℝ) := by
      exact ENNReal.lintegral_mul_norm_pow_le hmin hmax
        (by positivity) (by positivity) (by norm_num)
    calc
      hellingerMinMax ^ (2 : ℝ) ≤
          (affinity ^ (1 / 2 : ℝ) * opposite ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        gcongr
      _ = affinity * opposite := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
      _ ≤ affinity * 2 := mul_le_mul_right hopposite affinity
      _ = 2 * affinity := mul_comm _ _
  rw [hbridge, hhellinger] at hJ
  have hright_top : 2 * affinity ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ha_top
  have hCreal := ENNReal.toReal_mono hright_top hC
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul] at hCreal
  norm_num at hCreal
  have hexp_sq : Real.exp (-(klDiv P Q).toReal) =
      Real.exp (-(klDiv P Q).toReal / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (ENNReal.ofReal_le_iff_le_toReal ha_top).2
  rw [hexp_sq]
  have hexp_nonneg : 0 ≤ Real.exp (-(klDiv P Q).toReal / 2) := (Real.exp_pos _).le
  have hhellinger_nonneg : 0 ≤ hellingerMinMax.toReal := ENNReal.toReal_nonneg
  nlinarith

end FixedGapDependency6

section FixedGapInterface6


open MeasureTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.le_cam_inequality {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (2⁻¹ * Real.exp (-(klDiv P Q).toReal)) ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  apply FixedGapDependency6.checked <;> assumption

end FixedGapInterface6

/- Complete accepted source by jianglsbz, submission 41db277c-8f09-4f00-84e3-d867bfb59908. -/
namespace FixedGapDependency7
open _root_.BanditAlgorithm

open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem checked {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  let ν := P + Q
  have hPν : P ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hQν : Q ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' P
  have h_affinity :
      ∫⁻ ω, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν ≤ P A + Q Aᶜ := by
    calc
      ∫⁻ ω, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν =
          (∫⁻ ω in A, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν) +
            ∫⁻ ω in Aᶜ, min (P.rnDeriv ν ω) (Q.rnDeriv ν ω) ∂ν :=
        (lintegral_add_compl _ hA).symm
      _ ≤ (∫⁻ ω in A, P.rnDeriv ν ω ∂ν) +
            ∫⁻ ω in Aᶜ, Q.rnDeriv ν ω ∂ν := by
        exact add_le_add
          (setLIntegral_mono (Measure.measurable_rnDeriv _ _) fun _ _ ↦ min_le_left _ _)
          (setLIntegral_mono (Measure.measurable_rnDeriv _ _) fun _ _ ↦ min_le_right _ _)
      _ = P A + Q Aᶜ := by
        rw [Measure.setLIntegral_rnDeriv hPν, Measure.setLIntegral_rnDeriv hQν]
  have h_lecam := BanditAlgorithm.le_cam_inequality P Q hD
  have h_enn :
      ENNReal.ofReal (2⁻¹ * exp (-(klDiv P Q).toReal)) ≤
        ENNReal.ofReal (P.real A + Q.real Aᶜ) := by
    rw [ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg)]
    simpa [Measure.real, ν] using h_lecam.trans h_affinity
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_enn

end FixedGapDependency7

section FixedGapInterface7


open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem BanditAlgorithm.bretagnolle_huber_inequality {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    2⁻¹ * exp (-(klDiv P Q).toReal) ≤ P.real A + Q.real Aᶜ := by
  apply FixedGapDependency7.checked <;> assumption

end FixedGapInterface7


/-
Local measurable-count, Gaussian-mean, integrability and two-environment algebra
are adapted from the complete accepted proof by Harry_Xu,
theorem fa7b1426-1743-4773-bad5-c9471f4f47f9, submission 21943945-b02f-4a59-a648-62ce0e3ba583.
Original SHA-256: b8025f75267b13eda2234050753b3fb6624673ea3d47137d4f1de9c8447eb25e.
The assembly manifest records exact unchanged source selections.
All registered theorem proof closures and reused auxiliary proofs are included in this default port.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open BanditAlgorithm

/-!
Historical source context: these local helpers and the two-environment algebra
come from an accepted proof of Lattimore--Szepesvari Theorem 15.2, which tunes
the gap to obtain a minimax expected-regret bound. The theorem proved in this
file is instead the fixed-gap testing core of Theorem 17.1 (pp. 216--217).
Here Delta remains the arbitrary supplied gap; no tuning step is performed.
-/

private theorem measurable_armPullCount_pair {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem pull_count_sum_pair {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, (armPullCount i h : ℝ) = n := by
  rw [show (∑ i, (armPullCount i h : ℝ)) =
      ∑ i, ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm]
  rw [Finset.sum_comm]
  simp

private theorem gaussian_bandit_mean_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μ) i = μ i := by
  simp [banditArmMean, gaussianBandit]

private theorem gaussian_bandit_integrable_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) :
    Integrable id ((gaussianBandit μ).P i) := by
  apply memLp_one_iff_integrable.mp
  simpa [gaussianBandit] using
    (ProbabilityTheory.memLp_id_gaussianReal'
      (μ := μ i) (v := (1 : NNReal)) (1 : ENNReal) (by simp))

private theorem arm_pull_count_integrable_pair {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  have hprod := Integrable.bdd_mul
    (integrable_const (μ := banditMeasure ν π n) (1 : ℝ))
    (measurable_armPullCount_pair (n := n) i).aestronglyMeasurable
    (c := (n : ℝ)) (by
      filter_upwards [] with h
      rw [norm_natCast]
      exact_mod_cast (show armPullCount i h ≤ n by
        rw [armPullCount]
        simpa using (Finset.card_le_univ {t | ((h t).1 = i)}.toFinset)))
  simpa only [mul_one] using hprod

private theorem integral_ge_const_mul_measureReal
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f P) (hc : 0 ≤ c)
    (hfc : ∀ ω ∈ A, c ≤ f ω) (hf0 : ∀ ω, 0 ≤ f ω) :
    P.real A * c ≤ ∫ ω, f ω ∂P := by
  have hi : Integrable (A.indicator (fun _ : Ω ↦ c)) P :=
    (integrable_const c).indicator hA
  have hmono :
      ∫ ω, A.indicator (fun _ : Ω ↦ c) ω ∂P ≤ ∫ ω, f ω ∂P := by
    apply integral_mono hi hf
    intro ω
    by_cases hω : ω ∈ A
    · simpa [Set.indicator_of_mem hω] using hfc ω hω
    · simpa [Set.indicator, hω] using hf0 ω
  simpa [integral_indicator_const, hA, smul_eq_mul] using hmono

private theorem gaussian_optimal_mean_eq_pair {k : ℕ}
    (μ : Fin k → ℝ) (i : Fin k) (hmax : ∀ j, μ j ≤ μ i) :
    banditOptimalMean (gaussianBandit μ) = μ i := by
  letI : Nonempty (Fin k) := ⟨i⟩
  rw [banditOptimalMean]
  simp only [gaussian_bandit_mean_pair]
  apply le_antisymm
  · exact ciSup_le hmax
  · exact le_ciSup (Set.finite_range μ).bddAbove i

theorem solution {k n : ℕ}
    (hk : 2 ≤ k) (hn : 1 ≤ n) {B : ℝ} (hB : 0 < B) (π : BanditPolicy k)
    (hbound : ∀ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      banditRegret (gaussianBandit μvec) π n ≤ B * Real.sqrt (((k : ℝ) - 1) * n))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (Δ : ℝ)
    (hΔpos : 0 < Δ) (hΔle : Δ ≤ 1 / 2)
    (htest : 2 * δ ≤ (1 / 2 : ℝ) *
      Real.exp (-2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)))) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      δ ≤ (banditMeasure (gaussianBandit μvec) π n).real
        {h | Δ * n / 2 ≤
          ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} := by
  have hk : 1 < k := by omega
  have hΔ : Δ ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hΔpos.le, hΔle⟩
  classical
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, hk⟩
  let arms : Finset (Fin k) := Finset.univ.erase z
  have ho_ne : o ≠ z := by
    intro h
    have := congrArg Fin.val h
    simp [o, z] at this
  have harms : arms.Nonempty := by
    refine ⟨o, ?_⟩
    simp [arms, ho_ne]
  let μ : Fin k → ℝ := fun j ↦ if j = z then Δ else 0
  have hμbox : ∀ j, μ j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    by_cases hj : j = z
    · simp [μ, hj, hΔ.1, hΔ.2.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    · simp [μ, hj]
  have hopt : banditOptimalMean (gaussianBandit μ) = Δ := by
    apply gaussian_optimal_mean_eq_pair μ z
    intro j
    by_cases hj : j = z <;> simp [μ, hj, hΔ.1]
  have hgap (j : Fin k) :
      banditGap (gaussianBandit μ) j = if j = z then 0 else Δ := by
    rw [banditGap, hopt, gaussian_bandit_mean_pair]
    by_cases hj : j = z <;> simp [μ, hj]
  let pullMean : Fin k → ℝ := fun j ↦
    ∫ h, (armPullCount j h : ℝ) ∂banditMeasure (gaussianBandit μ) π n
  have hpull_nonneg (j : Fin k) : 0 ≤ pullMean j := by
    dsimp [pullMean]
    exact integral_nonneg (fun h ↦ by positivity)
  obtain ⟨i, hiarms, hmin⟩ := arms.exists_min_image pullMean harms
  have hiz : i ≠ z := by
    simpa [arms] using (Finset.mem_erase.mp hiarms).1
  have hcard : (arms.card : ℝ) = (k : ℝ) - 1 := by
    simp [arms, Nat.cast_sub (by omega : 1 ≤ k)]
  have havg : (arms.card : ℝ) * pullMean i ≤
      ∑ j ∈ arms, pullMean j := by
    calc
      (arms.card : ℝ) * pullMean i = ∑ _j ∈ arms, pullMean i := by simp
      _ ≤ ∑ j ∈ arms, pullMean j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmin j hj
  have hk0 : 0 < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hregP : banditRegret (gaussianBandit μ) π n =
      Δ * ∑ j ∈ arms, pullMean j := by
    rw [bandit_regret_decomposition (gaussianBandit μ)
      (gaussian_bandit_integrable_pair μ) π n]
    simp only [hgap, pullMean]
    rw [show (∑ j, (if j = z then 0 else Δ) *
          ∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n) =
        ∑ j ∈ arms, Δ *
          ∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n by
      let f : Fin k → ℝ := fun j ↦ (if j = z then 0 else Δ) *
        ∫ h, (armPullCount j h : ℝ)
          ∂banditMeasure (gaussianBandit μ) π n
      have hfz : f z = 0 := by simp [f]
      change (∑ j, f j) = _
      rw [← Finset.sum_erase Finset.univ hfz]
      apply Finset.sum_congr
      · rfl
      · intro j hj
        have hjz : j ≠ z := (Finset.mem_erase.mp hj).1
        simp [f, hjz, arms]]
    rw [← Finset.mul_sum]
  have hEi : pullMean i ≤
      B * Real.sqrt (((k : ℝ) - 1) * n) / (Δ * ((k : ℝ) - 1)) := by
    apply (le_div_iff₀ (mul_pos hΔpos hk0)).2
    calc
      pullMean i * (Δ * ((k : ℝ) - 1)) = Δ * ((arms.card : ℝ) * pullMean i) := by
        rw [hcard]
        ring
      _ ≤ Δ * ∑ j ∈ arms, pullMean j := mul_le_mul_of_nonneg_left havg hΔpos.le
      _ = banditRegret (gaussianBandit μ) π n := hregP.symm
      _ ≤ B * Real.sqrt (((k : ℝ) - 1) * n) := hbound μ hμbox

  let μ' : Fin k → ℝ := fun j ↦ if j = i then 2 * Δ else μ j
  have hμ'box : ∀ j, μ' j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    by_cases hj : j = i
    · simp [μ', hj, hΔ.1]
      linarith [hΔ.2]
    · simpa [μ', hj] using hμbox j
  have hopt' : banditOptimalMean (gaussianBandit μ') = 2 * Δ := by
    calc
      banditOptimalMean (gaussianBandit μ') = μ' i := by
        apply gaussian_optimal_mean_eq_pair μ' i
        intro j
        rw [show μ' i = 2 * Δ by simp [μ']]
        by_cases hji : j = i
        · simp [μ', hji]
        · rw [show μ' j = μ j by simp [μ', hji]]
          by_cases hjz : j = z
          · simp [μ, hjz]
            linarith [hΔ.1]
          · simp [μ, hjz, hΔ.1]
      _ = 2 * Δ := by simp [μ']
  have hgap' (j : Fin k) :
      banditGap (gaussianBandit μ') j =
        if j = i then 0 else if j = z then Δ else 2 * Δ := by
    rw [banditGap, hopt', gaussian_bandit_mean_pair]
    by_cases hji : j = i
    · simp [μ', hji]
    · rw [show μ' j = μ j by simp [μ', hji]]
      by_cases hjz : j = z
      · subst j
        simp [μ, Ne.symm hiz]
        ring
      · simp [μ, hji, hjz]
  have hkl_arm (j : Fin k) :
      klDiv ((gaussianBandit μ).P j) ((gaussianBandit μ').P j) =
        if j = i then ENNReal.ofReal (2 * Δ ^ 2) else 0 := by
    change klDiv (gaussianReal (μ j) 1) (gaussianReal (μ' j) 1) = _
    rw [gaussian_relative_entropy_formula (μ j) (μ' j) (by norm_num)]
    by_cases hj : j = i
    · subst j
      rw [if_pos rfl]
      have hmui : μ i = 0 := by simp [μ, hiz]
      have hmupi : μ' i = 2 * Δ := by simp [μ']
      rw [hmui, hmupi]
      congr 1
      norm_num
      ring
    · rw [if_neg hj]
      have hmueq : μ' j = μ j := by simp [μ', hj]
      rw [hmueq]
      simp
  have hKLfinite (j : Fin k) :
      klDiv ((gaussianBandit μ).P j) ((gaussianBandit μ').P j) ≠ ⊤ := by
    rw [hkl_arm]
    split
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top
  have hdiv := bandit_divergence_decomposition
    (gaussianBandit μ) (gaussianBandit μ') hKLfinite π n
  have hDtoReal :
      (klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n)).toReal =
          pullMean i * (2 * Δ ^ 2) := by
    rw [hdiv]
    simp only [hkl_arm]
    rw [show (∑ j, ENNReal.ofReal
          (∫ h, (armPullCount j h : ℝ)
            ∂banditMeasure (gaussianBandit μ) π n) *
          (if j = i then ENNReal.ofReal (2 * Δ ^ 2) else 0)) =
        ENNReal.ofReal (pullMean i) * ENNReal.ofReal (2 * Δ ^ 2) by
      simp [pullMean]]
    rw [← ENNReal.ofReal_mul (hpull_nonneg i)]
    rw [ENNReal.toReal_ofReal]
    positivity
  have hDfinite :
      klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n) ≠ ⊤ := by
    rw [hdiv]
    apply ENNReal.sum_ne_top.2
    intro j hj
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKLfinite j)
  have hroot : Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1) =
      Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
    calc
      Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1) =
          Real.sqrt (n : ℝ) * (Real.sqrt ((k : ℝ) - 1) / ((k : ℝ) - 1)) := by
        rw [Real.sqrt_mul hk0.le]
        ring
      _ = Real.sqrt (n : ℝ) / Real.sqrt ((k : ℝ) - 1) := by
        rw [Real.sqrt_div_self']
        ring
      _ = Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) :=
        (Real.sqrt_div (Nat.cast_nonneg n) _).symm
  have hDle :
      (klDiv (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n)).toReal ≤
          2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by
    rw [hDtoReal]
    calc
      pullMean i * (2 * Δ ^ 2) ≤
          (B * Real.sqrt (((k : ℝ) - 1) * n) / (Δ * ((k : ℝ) - 1))) * (2 * Δ ^ 2) :=
        mul_le_mul_of_nonneg_right hEi (by positivity)
      _ = 2 * B * Δ * (Real.sqrt (((k : ℝ) - 1) * n) / ((k : ℝ) - 1)) := by
        field_simp [hΔpos.ne', hk0.ne']
        <;> ring
      _ = 2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)) := by rw [hroot]

  let P := banditMeasure (gaussianBandit μ) π n
  let Q := banditMeasure (gaussianBandit μ') π n
  let A : Set (BanditHistory k n) :=
    {h | (armPullCount z h : ℝ) ≤ (n : ℝ) / 2}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_armPullCount_pair z) measurable_const
  have hBH :
      (1 / 2 : ℝ) * Real.exp (-(klDiv P Q).toReal) ≤
        P.real A + Q.real Aᶜ := by
    simpa [P, Q] using
      (bretagnolle_huber_inequality
        (banditMeasure (gaussianBandit μ) π n)
        (banditMeasure (gaussianBandit μ') π n) hA hDfinite)
  have hprob : 2 * δ ≤ P.real A + Q.real Aᶜ := by
    refine htest.trans ((mul_le_mul_of_nonneg_left ?_ (by norm_num)).trans hBH)
    apply Real.exp_le_exp.mpr
    have hd := neg_le_neg hDle
    simpa [P, Q] using hd
  by_cases hPA : δ ≤ P.real A
  · refine ⟨μ, hμbox, hPA.trans (measureReal_mono ?_)⟩
    intro h hh
    have hzle : (armPullCount z h : ℝ) ≤ (n : ℝ) / 2 := hh
    have hsplit : (∑ j ∈ arms, (armPullCount j h : ℝ)) +
        (armPullCount z h : ℝ) = n := by
      rw [← pull_count_sum_pair h]
      simpa [arms] using
        (Finset.sum_erase_add (f := fun j ↦ (armPullCount j h : ℝ)) (Finset.mem_univ z))
    have hhalf : (n : ℝ) / 2 ≤ ∑ j ∈ arms, (armPullCount j h : ℝ) := by linarith
    change Δ * n / 2 ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j
    calc
      Δ * n / 2 = Δ * ((n : ℝ) / 2) := by ring
      _ ≤ Δ * ∑ j ∈ arms, (armPullCount j h : ℝ) :=
        mul_le_mul_of_nonneg_left hhalf hΔpos.le
      _ = ∑ j ∈ arms, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjz : j ≠ z := (Finset.mem_erase.mp hj).1
        rw [hgap j, if_neg hjz]
        ring
      _ ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ) j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ arms)
        intro j hj hjout
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hgap]
        split_ifs <;> positivity
  · have hQA : δ ≤ Q.real Aᶜ := by linarith [lt_of_not_ge hPA]
    refine ⟨μ', hμ'box, hQA.trans (measureReal_mono ?_)⟩
    intro h hh
    have hzgt : (n : ℝ) / 2 < (armPullCount z h : ℝ) := by simpa [A] using hh
    have hterm : (armPullCount z h : ℝ) * banditGap (gaussianBandit μ') z ≤
        ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin k => (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j)
        _ (Finset.mem_univ z)
      intro j hj
      apply mul_nonneg (Nat.cast_nonneg _)
      rw [hgap']
      split_ifs <;> positivity
    have hgapz : banditGap (gaussianBandit μ') z = Δ := by
      rw [hgap' z, if_neg (Ne.symm hiz), if_pos rfl]
    change Δ * n / 2 ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j
    calc
      Δ * n / 2 = ((n : ℝ) / 2) * Δ := by ring
      _ ≤ (armPullCount z h : ℝ) * Δ := mul_le_mul_of_nonneg_right hzgt.le hΔpos.le
      _ = (armPullCount z h : ℝ) * banditGap (gaussianBandit μ') z := by rw [hgapz]
      _ ≤ ∑ j, (armPullCount j h : ℝ) * banditGap (gaussianBandit μ') j := hterm


#print axioms solution
