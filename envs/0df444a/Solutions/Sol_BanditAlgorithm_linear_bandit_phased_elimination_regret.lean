-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_phased_elimination_regret
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:29:46.293271+00:00
-- url     : https://prove2.me/submissions/95ea1409-504a-4d11-b224-48cdb584cf4c

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FunProp
import Definitions.Def_BanditPolicy
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_StochasticLinearBandit
import Definitions.Def_banditRegret
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

/-! Finite stochastic linear-bandit phased elimination, with constant 1024.
The exact integer-design variant proves the posted policy-existence statement;
it is not the rounded allocation of textbook Algorithm 12. Arms may be rank-deficient
and have arbitrary norms. The policy is selected before the unknown model.
All three accepted canonical expectation dependency bodies are embedded below.
The complete prior local proof components are retained with explicit elaboration
compatibility corrections for the pinned default environment. -/

/- Accepted dependency c38ebcad-a56f-4165-8700-432fd166d15c; author MKPynnic; submission cdf45b26-c875-4abc-836c-d40d8b44fafc.
+Source SHA256 de02061bac2d15744d477de8c160851b0c777f7bc19c57b5d6788d8edaa90c42. Complete body, with final theorem alias renamed. -/
section
/-!
Direct-proof work for Lattimore--Szepesvári, Lemma 4.5, printed p. 63:
the canonical reward drawn after selecting arm `i` has conditional mean `μ_i`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem banditRewardKernel_apply_rfl' {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    banditRewardKernel ν i = ν.P i := rfl

theorem stepKernel_centered_integrable_test {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ)
    (h : BanditHistory k n) :
    Integrable (fun z : Fin k × ℝ ↦ z.2 - banditArmMean ν z.1)
      (banditStepKernel ν π n h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff (by fun_prop)).2
  constructor
  · exact Filter.Eventually.of_forall fun i ↦ by
      have hsub : Integrable (fun y : ℝ ↦ y - banditArmMean ν i) (ν.P i) :=
        (hInt i).sub (integrable_const (banditArmMean ν i))
      simpa [banditRewardKernel_apply_rfl'] using hsub
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
  have hy : Integrable (fun y : ℝ ↦ y) (ν.P i) := hInt i
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

theorem BanditAlgorithm.bandit_expected_reward_eq_arm_occupation {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.banditMeasure ν π n) =
      ∑ i, BanditAlgorithm.banditArmMean ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n) := by
  exact BanditAlgorithm.expected_reward_eq_arm_occupation_test ν hInt π n
end

/- Accepted dependency 1ce46403-6a8e-4d87-b2c8-dfefe1480160; author MKPynnic; submission 395053eb-8de2-4af3-a2e7-51a2c2456ee0.
+Source SHA256 99a2b3c189e2ef9710e972aa19fcfc71c89443230c1e0d042b6bb96256f35b6c. Complete body, with final theorem alias renamed. -/
section
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

theorem BanditAlgorithm.bandit_canonical_occupation_identities {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
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
end

/- Accepted dependency 9c4b9d59-c480-4e0c-9619-d7ef8f84d3c2; author MKPynnic; submission 9ef8307f-053a-4d4d-8034-3a088a5e5397.
+Source SHA256 3c9f0201886c8ceddb8ddd8aa7a495fde572c1340499ef475e6db1ca8e63d72c. Complete body, with final theorem alias renamed. -/
section
/-!
Source-faithful reduction of Lattimore and Szepesvári, *Bandit Algorithms*
(CUP 2020), Lemma 4.5, printed pp. 62--63.  The imported child isolates the
conditional-reward and occupation-count identities proved around Eq. (4.6).
This file performs the remaining gap-weighted finite-sum algebra.
-/

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_regret_decomposition {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
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
end

/- Complete adapted prior component: PhaseNumerics. -/
section
open MeasureTheory
open scoped BigOperators

namespace PhasedElimination

def phaseLength (M l : Nat) : Nat := M * 4 ^ l

def phaseStart (M l : Nat) : Nat :=
  ∑ q ∈ Finset.range l, phaseLength M q

noncomputable def phaseRadius (l : Nat) : Real := (1 / 2) ^ l

theorem phaseStart_zero (M : Nat) : phaseStart M 0 = 0 := by
  simp [phaseStart]

theorem phaseStart_succ (M l : Nat) :
    phaseStart M (l + 1) = phaseStart M l + phaseLength M l := by
  simp [phaseStart, Finset.sum_range_succ]

theorem phaseLength_pos {M : Nat} (hM : 0 < M) (l : Nat) :
    0 < phaseLength M l := by
  exact Nat.mul_pos hM (pow_pos (by decide) _)

theorem phaseStart_mono (M : Nat) : Monotone (phaseStart M) := by
  apply monotone_nat_of_le_succ
  intro l
  rw [phaseStart_succ]
  omega

theorem previous_phase_le_start (M l : Nat) :
    phaseLength M l ≤ phaseStart M (l + 1) := by
  rw [phaseStart_succ]
  omega

theorem phaseStart_covers {M n : Nat} (hM : 0 < M) :
    n ≤ phaseStart M (Nat.clog 2 n + 1) := by
  calc
    n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide) _
    _ ≤ 4 ^ Nat.clog 2 n := Nat.pow_le_pow_left (by decide) _
    _ ≤ phaseLength M (Nat.clog 2 n) := by
      unfold phaseLength
      simpa using Nat.mul_le_mul_right (4 ^ Nat.clog 2 n) hM
    _ ≤ phaseStart M (Nat.clog 2 n + 1) := previous_phase_le_start _ _

theorem phase_weight_identity (M l : Nat) :
    (phaseLength M l : Real) * (8 * phaseRadius l) = 8 * M * 2 ^ l := by
  simp only [phaseLength, phaseRadius, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (M : Real) * 4 ^ l * (8 * (1 / 2) ^ l) =
        8 * M * (4 * (1 / 2)) ^ l := by rw [mul_pow]; ring
    _ = 8 * M * 2 ^ l := by norm_num

theorem phase_weight_sum_le (M m : Nat) :
    (∑ l ∈ Finset.range (m + 1),
      (phaseLength M l : Real) * (8 * phaseRadius l)) ≤ 16 * M * 2 ^ m := by
  simp_rw [phase_weight_identity]
  have aux (q : Nat) : (∑ l ∈ Finset.range q, (2 : Real) ^ l) = 2 ^ q - 1 := by
    induction q with
    | zero => simp
    | succ q ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [← Finset.mul_sum, aux, pow_succ]
  have hM : (0 : Real) ≤ M := Nat.cast_nonneg _
  nlinarith

theorem phase_regret_bound {M n m : Nat} {R : Real}
    (hR : R ≤ n) (hstart : phaseStart M m ≤ n)
    (hend : n ≤ phaseStart M (m + 1))
    (hphase : R ≤ ∑ l ∈ Finset.range (m + 1),
      (phaseLength M l : Real) * (8 * phaseRadius l)) :
    R ≤ 32 * Real.sqrt ((n : Real) * M) := by
  have hs := Real.sq_sqrt (show (0 : Real) ≤ n * M by positivity)
  have hp := Real.sqrt_nonneg ((n : Real) * M)
  cases m with
  | zero =>
      have hnM : n ≤ M := by simpa [phaseStart, phaseLength] using hend
      have hsq : (n : Real) ^ 2 ≤ (n : Real) * M := by
        rw [pow_two]
        exact_mod_cast Nat.mul_le_mul_left n hnM
      have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg _
      nlinarith
  | succ m =>
      have hmn : M * 4 ^ m ≤ n := (previous_phase_le_start M m).trans hstart
      have hmn' : (M : Real) * 4 ^ m ≤ n := by exact_mod_cast hmn
      have hpow : (2 : Real) ^ m * 2 ^ m = 4 ^ m := by
        rw [← mul_pow]
        norm_num
      have hM : (0 : Real) ≤ M := Nat.cast_nonneg _
      have hx : (0 : Real) ≤ (M : Real) * 2 ^ m := by positivity
      have hsq : ((M : Real) * 2 ^ m) ^ 2 ≤ (n : Real) * M := by
        calc
          ((M : Real) * 2 ^ m) ^ 2 = ((M : Real) * 4 ^ m) * M := by
            rw [mul_pow, pow_two ((2 : Real) ^ m), hpow]
            ring
          _ ≤ (n : Real) * M := mul_le_mul_of_nonneg_right hmn' hM
      have hroot : (M : Real) * 2 ^ m ≤ Real.sqrt ((n : Real) * M) := by
        nlinarith
      have hb := hphase.trans (phase_weight_sum_le M (m + 1))
      rw [pow_succ] at hb
      nlinarith

end PhasedElimination
end

/- Complete adapted prior component: PhaseParameters. -/
section
namespace PhasedElimination

def confidencePhases (n : Nat) : Nat := Nat.clog 2 n + 1

noncomputable def confidenceLog (k n : Nat) (delta : Real) : Real :=
  Real.log (2 * k * confidencePhases n / delta)

noncomputable def basePhaseLength (k d n : Nat) (delta : Real) : Nat :=
  Nat.ceil (8 * d * confidenceLog k n delta) + 2 * d

theorem confidencePhases_pos (n : Nat) : 0 < confidencePhases n := by
  unfold confidencePhases
  omega

theorem log_horizon_lower {n : Nat} (hn : 2 ≤ n) :
    (2 / 3 : Real) ≤ Real.log n := by
  have h := Real.log_le_log (show (0 : Real) < 2 by norm_num)
    (show (2 : Real) ≤ n by exact_mod_cast hn)
  linarith [Real.log_two_gt_d9]

theorem confidencePhases_le_log {n : Nat} (hn : 2 ≤ n) :
    (confidencePhases n : Real) ≤ 5 * Real.log n := by
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := log_horizon_lower hn
  have hceil := Nat.ceil_lt_add_one
    (Real.logb_nonneg (show (1 : Real) < 2 by norm_num) hn1)
  have hc : Nat.ceil (Real.logb 2 (n : Real)) = Nat.clog 2 n := by
    simpa using Real.natCeil_logb_natCast 2 n
  rw [hc] at hceil
  have hdiv : Real.log (n : Real) / Real.log 2 ≤ 2 * Real.log n := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).2
    nlinarith [Real.log_two_gt_d9]
  simp only [Real.logb] at hceil
  unfold confidencePhases
  push_cast
  linarith

theorem confidencePhases_le_twice {n : Nat} (hn : 1 ≤ n) :
    confidencePhases n ≤ 2 * n := by
  have h : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow
    (Nat.le_of_lt (Nat.lt_pow_self (show 1 < 2 by decide)))
  unfold confidencePhases
  omega

theorem confidenceLog_lower {k n : Nat} {delta : Real}
    (hk : 2 ≤ k) (hd0 : 0 < delta) (hd1 : delta < 1) :
    1 ≤ confidenceLog k n delta := by
  have hH : (1 : Real) ≤ confidencePhases n := by
    exact_mod_cast confidencePhases_pos n
  have hK : (2 : Real) ≤ k := by exact_mod_cast hk
  have hprod : (4 : Real) ≤ 2 * k * confidencePhases n := by
    nlinarith [mul_le_mul hK hH (by norm_num) (by positivity : (0 : Real) ≤ k)]
  have harg : (4 : Real) ≤ 2 * k * confidencePhases n / delta :=
    (le_div_iff₀ hd0).2 (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : Real) < 4) harg
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold confidenceLog
  linarith [Real.log_two_gt_d9]

theorem targetLog_lower {k n : Nat} {delta : Real}
    (hk : 2 ≤ k) (hn : 2 ≤ n) (hd0 : 0 < delta) (hd1 : delta < 1) :
    (1 / 4 : Real) ≤ Real.log (k * Real.log n / delta) := by
  have hK : (2 : Real) ≤ k := by exact_mod_cast hk
  have hlog := log_horizon_lower hn
  have hprod : (4 / 3 : Real) ≤ k * Real.log n := by
    nlinarith [mul_le_mul hK hlog (by norm_num) (by positivity : (0 : Real) ≤ k)]
  have harg : (4 / 3 : Real) ≤ k * Real.log n / delta :=
    (le_div_iff₀ hd0).2 (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : Real) < 4 / 3) harg
  have hlower := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 4 / 3)
  norm_num at hlower
  linarith

theorem confidenceLog_le_target {k n : Nat} {delta : Real}
    (hk : 2 ≤ k) (hn : 2 ≤ n) (hd0 : 0 < delta) (hd1 : delta < 1) :
    confidenceLog k n delta ≤ 40 * Real.log (k * Real.log n / delta) := by
  have hH := confidencePhases_le_log hn
  have hK : (0 : Real) ≤ k := Nat.cast_nonneg _
  have harg : 2 * k * confidencePhases n / delta ≤
      10 * (k * Real.log n / delta) := by
    have h := mul_le_mul_of_nonneg_left hH (show (0 : Real) ≤ 2 * k by positivity)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith [h]) hd0.le
  have hp : (0 : Real) < 2 * k * confidencePhases n / delta := by
    have := confidencePhases_pos n
    have : 0 < k := by omega
    positivity
  have hx : (0 : Real) < k * Real.log n / delta := by
    have := log_horizon_lower hn
    have : 0 < k := by omega
    positivity
  have h := Real.log_le_log hp harg
  rw [Real.log_mul (by norm_num) (ne_of_gt hx)] at h
  have hten := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
  have hlower := targetLog_lower hk hn hd0 hd1
  unfold confidenceLog
  linarith

theorem basePhaseLength_bounds {k d n : Nat} {delta : Real}
    (hk : 2 ≤ k) (hd : 0 < d) (hd0 : 0 < delta) (hd1 : delta < 1) :
    8 * d * confidenceLog k n delta ≤ (basePhaseLength k d n delta : Real) ∧
    2 * d ≤ basePhaseLength k d n delta ∧
    (basePhaseLength k d n delta : Real) ≤ 11 * d * confidenceLog k n delta := by
  have hb := confidenceLog_lower (n := n) hk hd0 hd1
  have hdR : (1 : Real) ≤ d := by exact_mod_cast hd
  have hx : 0 ≤ 8 * d * confidenceLog k n delta := by positivity
  have hlo := Nat.le_ceil (8 * d * confidenceLog k n delta)
  have hhi := Nat.ceil_lt_add_one hx
  unfold basePhaseLength
  push_cast
  constructor
  · linarith
  constructor
  · omega
  · have hp := mul_le_mul_of_nonneg_left hb (show (0 : Real) ≤ d by positivity)
    nlinarith

end PhasedElimination
end

/- Complete adapted prior component: PhaseExpectation. -/
section
open MeasureTheory

namespace PhasedElimination

theorem integral_le_of_high_probability {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {X : Omega → Real}
    (hX : Measurable X) (hInt : Integrable X mu) {B N delta : Real}
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hBound : ∀ w, X w ≤ N)
    (hGood : 1 - delta ≤ mu.real {w | X w ≤ B}) :
    (∫ w, X w ∂mu) ≤ B + N * delta := by
  let G : Set Omega := {w | X w ≤ B}
  have hG : MeasurableSet G := measurableSet_le hX measurable_const
  have hBad : mu.real Gᶜ ≤ delta := by
    rw [measureReal_compl hG, probReal_univ]
    change 1 - mu.real {w | X w ≤ B} ≤ delta
    linarith
  have hIndicator : Integrable (Gᶜ.indicator (fun _ : Omega ↦ N)) mu :=
    (integrable_const N).indicator hG.compl
  have hDom (w : Omega) : X w ≤ B + Gᶜ.indicator (fun _ ↦ N) w := by
    by_cases hw : w ∈ G
    · have hg : X w ≤ B := hw
      simpa [Set.indicator_of_notMem (show w ∉ Gᶜ by simpa using hw)] using hg
    · have hg : w ∈ Gᶜ := hw
      rw [Set.indicator_of_mem hg]
      linarith [hBound w]
  calc
    (∫ w, X w ∂mu) ≤ ∫ w, B + Gᶜ.indicator (fun _ ↦ N) w ∂mu :=
      integral_mono hInt ((integrable_const B).add hIndicator) hDom
    _ = B + mu.real Gᶜ * N := by
      rw [integral_add (integrable_const B) hIndicator, integral_indicator hG.compl]
      simp [Measure.real, smul_eq_mul]
    _ ≤ B + N * delta := by
      nlinarith [mul_le_mul_of_nonneg_right hBad hN]

end PhasedElimination
end

/- Complete adapted prior component: ExactDesignAlgebra. -/
section
open Matrix
open scoped BigOperators

namespace PhasedElimination

def gram {d T : Nat} (x : Fin T -> Fin d -> Real) : Matrix (Fin d) (Fin d) Real :=
  ∑ t, vecMulVec (x t) (x t)

def ridge {d T : Nat} (e : Real) (x : Fin T -> Fin d -> Real) :
    Matrix (Fin d) (Fin d) Real := e • 1 + gram x

theorem gram_posSemidef {d T : Nat} (x : Fin T -> Fin d -> Real) :
    (gram x).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro t _
  have hs : star (x t) = x t := by ext i; rfl
  simpa only [hs] using Matrix.posSemidef_vecMulVec_self_star (x t)

theorem ridge_posDef {d T : Nat} {e : Real} (he : 0 < e)
    (x : Fin T -> Fin d -> Real) : (ridge e x).PosDef :=
  (Matrix.PosDef.one.smul he).add_posSemidef (gram_posSemidef x)

theorem gram_energy {d T : Nat} (x : Fin T -> Fin d -> Real) (z : Fin d -> Real) :
    z ⬝ᵥ gram x *ᵥ z = ∑ t, (x t ⬝ᵥ z)^2 := by
  simp only [gram, Matrix.sum_mulVec, dotProduct_sum, Matrix.vecMulVec_mulVec,
    dotProduct_smul, op_smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [dotProduct_comm z (x t)]
  ring

theorem ridge_energy {d T : Nat} (e : Real) (x : Fin T -> Fin d -> Real)
    (z : Fin d -> Real) :
    z ⬝ᵥ ridge e x *ᵥ z = e * (z ⬝ᵥ z) + ∑ t, (x t ⬝ᵥ z)^2 := by
  simp only [ridge, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, gram_energy]

theorem determinant_swap {d : Nat} {M : Matrix (Fin d) (Fin d) Real}
    (hM : M.IsSymm) (hdet : IsUnit M.det) (x y : Fin d -> Real) :
    (M - vecMulVec x x + vecMulVec y y).det = M.det *
      ((1 - x ⬝ᵥ M⁻¹ *ᵥ x) * (1 + y ⬝ᵥ M⁻¹ *ᵥ y) +
        (x ⬝ᵥ M⁻¹ *ᵥ y)^2) := by
  let U : Matrix (Fin d) (Fin 2) Real := fun i j => if j = 0 then -x i else y i
  let V : Matrix (Fin 2) (Fin d) Real := fun i j => if i = 0 then x j else y j
  have hUV : M + U * V = M - vecMulVec x x + vecMulVec y y := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
    simp [U, V, Fin.sum_univ_two, Matrix.vecMulVec_apply]
    ring
  have hs : y ⬝ᵥ M⁻¹ *ᵥ x = x ⬝ᵥ M⁻¹ *ᵥ y := by
    simpa only [hM.inv.eq] using Matrix.dotProduct_transpose_mulVec M⁻¹ y x
  have hsmall : 1 + V * M⁻¹ * U =
      !![1 - x ⬝ᵥ M⁻¹ *ᵥ x, x ⬝ᵥ M⁻¹ *ᵥ y;
        -(x ⬝ᵥ M⁻¹ *ᵥ y), 1 + y ⬝ᵥ M⁻¹ *ᵥ y] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply] <;>
      simp [U, V, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Finset.sum_neg_distrib, sub_eq_add_neg]
    simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum] using hs
  rw [← hUV, Matrix.det_add_mul U V hdet, hsmall, Matrix.det_fin_two_of]
  ring

theorem sum_leverage_le_dimension {d T : Nat} {e : Real} (he : 0 < e)
    (x : Fin T -> Fin d -> Real) :
    ∑ t, x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ x t <= (d : Real) := by
  let M := ridge e x
  have hM : M.PosDef := ridge_posDef he x
  have htrace : 0 <= M⁻¹.trace := by
    exact Finset.sum_nonneg fun i _ => hM.inv.posSemidef.diag_nonneg
  have hsum : ∑ t, x t ⬝ᵥ M⁻¹ *ᵥ x t = (M⁻¹ * gram x).trace := by
    simp only [gram, Finset.mul_sum, Matrix.trace_sum, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec]
    apply Finset.sum_congr rfl
    intro t _
    exact dotProduct_comm _ _
  have hmatrix : M⁻¹ * gram x = 1 - e • M⁻¹ := by
    have h := Matrix.nonsing_inv_mul M (hM.isUnit.map Matrix.detMonoidHom)
    change M⁻¹ * (e • 1 + gram x) = 1 at h
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
    exact eq_sub_of_add_eq' h
  rw [hsum, hmatrix, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  exact sub_le_self _ (mul_nonneg he.le htrace)

theorem ridge_weights_energy {d T : Nat} {e : Real} (he : 0 < e)
    (x : Fin T -> Fin d -> Real) (y : Fin d -> Real) :
    e * ((ridge e x)⁻¹ *ᵥ y ⬝ᵥ (ridge e x)⁻¹ *ᵥ y) +
        ∑ t, (x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ y)^2 = y ⬝ᵥ (ridge e x)⁻¹ *ᵥ y := by
  have hM := ridge_posDef he x
  rw [← ridge_energy, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hM.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec,
    dotProduct_comm]

theorem gram_update {d T : Nat} (x : Fin T -> Fin d -> Real)
    (t : Fin T) (y : Fin d -> Real) :
    gram (Function.update x t y) = gram x - vecMulVec (x t) (x t) + vecMulVec y y := by
  classical
  have hf : (fun s => vecMulVec (Function.update x t y s) (Function.update x t y s)) =
      Function.update (fun s => vecMulVec (x s) (x s)) t (vecMulVec y y) := by
    exact Function.comp_update (fun z => vecMulVec z z) x t y
  rw [gram, hf, Finset.sum_update_of_mem (Finset.mem_univ t),
    Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun s => vecMulVec (x s) (x s))
    (Finset.mem_univ t)
  change _ = (∑ s, vecMulVec (x s) (x s)) - _ + _
  rw [← hsum]
  abel

theorem ridge_update {d T : Nat} (e : Real) (x : Fin T -> Fin d -> Real)
    (t : Fin T) (y : Fin d -> Real) :
    ridge e (Function.update x t y) = ridge e x - vecMulVec (x t) (x t) +
      vecMulVec y y := by
  rw [ridge, gram_update, ridge]
  abel

theorem ridge_leverage_bound {d T : Nat} (hd : 0 < d) (hT : 2 * d <= T)
    {e : Real} (he : 0 < e) (x : Fin T -> Fin d -> Real) (y : Fin d -> Real)
    (hmax : forall t, (ridge e (Function.update x t y)).det <= (ridge e x).det) :
    y ⬝ᵥ (ridge e x)⁻¹ *ᵥ y <= 2 * (d : Real) / T := by
  let M := ridge e x
  let v := y ⬝ᵥ M⁻¹ *ᵥ y
  let u := fun t => x t ⬝ᵥ M⁻¹ *ᵥ x t
  have hM : M.PosDef := ridge_posDef he x
  have hsymm : M.IsSymm := by
    change M.transpose = M
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hM.isHermitian
  have hv : 0 <= v := by
    simpa only [v, star_trivial] using hM.inv.posSemidef.dotProduct_mulVec_nonneg y
  have hone (t : Fin T) : (1 - u t) * v <= u t := by
    have h := hmax t
    rw [ridge_update, determinant_swap hsymm (hM.isUnit.map Matrix.detMonoidHom)] at h
    have hfactor : (1 - u t) * (1 + v) + (x t ⬝ᵥ M⁻¹ *ᵥ y)^2 <= 1 := by
      apply (mul_le_mul_iff_right₀ hM.det_pos).mp
      simpa only [mul_one, one_mul, mul_comm, M, u, v] using h
    nlinarith [sq_nonneg (x t ⬝ᵥ M⁻¹ *ᵥ y)]
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hone t)
  have hdim : (∑ t, u t) <= (d : Real) := sum_leverage_le_dimension he x
  have hsum' : ((T : Real) - ∑ t, u t) * v <= ∑ t, u t := by
    simpa only [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hsum
  have hTreal : 2 * (d : Real) <= (T : Real) := by exact_mod_cast hT
  have hdreal : 0 < (d : Real) := by exact_mod_cast hd
  have hTpos : 0 < (T : Real) := by linarith
  apply (le_div_iff₀ hTpos).2
  have hnonneg := mul_nonneg (sub_nonneg.mpr hdim) hv
  have hnonneg' := mul_nonneg (sub_nonneg.mpr hTreal) hv
  nlinarith

theorem ridge_reconstruction {d T : Nat} {e : Real} (he : 0 < e)
    (x : Fin T -> Fin d -> Real) (y : Fin d -> Real) (q : Fin d) :
    (∑ t, (x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ y) * x t q) - y q =
      -(e * ((ridge e x)⁻¹ *ᵥ y) q) := by
  have hM := ridge_posDef he x
  have hsolve : ridge e x *ᵥ ((ridge e x)⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (hM.isUnit.map Matrix.detMonoidHom), Matrix.one_mulVec]
  have hq := congrFun hsolve q
  simp only [ridge, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    gram, Matrix.sum_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hq
  change e * ((ridge e x)⁻¹ *ᵥ y) q +
    (∑ t, (x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ y) * x t q) = y q at hq
  linarith

theorem ridge_weights_bounds {d T : Nat} {e C : Real} (he : 0 < e)
    (x : Fin T -> Fin d -> Real) (y : Fin d -> Real)
    (hv : y ⬝ᵥ (ridge e x)⁻¹ *ᵥ y <= C) :
    (∑ t, (x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ y)^2 <= C) ∧
    (forall q, ((∑ t, (x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ y) * x t q) - y q)^2 <= e * C) := by
  let z := (ridge e x)⁻¹ *ᵥ y
  have hz : 0 <= z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hs : 0 <= ∑ t, (x t ⬝ᵥ z)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have henergy := ridge_weights_energy he x y
  change e * (z ⬝ᵥ z) + ∑ t, (x t ⬝ᵥ z)^2 = _ at henergy
  have hez := mul_nonneg he.le hz
  constructor
  · linarith
  · intro q
    rw [ridge_reconstruction he]
    have hq : (z q)^2 <= z ⬝ᵥ z := by
      simpa only [dotProduct, pow_two] using
        (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (z i))
          (Finset.mem_univ q))
    have hbound : e * (z ⬝ᵥ z) <= C := by linarith
    have hq' := mul_le_mul_of_nonneg_left hq (sq_nonneg e)
    have hbound' := mul_le_mul_of_nonneg_left hbound he.le
    change (-(e * z q))^2 <= e * C
    nlinarith

end PhasedElimination
end

/- Complete adapted prior component: ExactDesign. -/
section
open Matrix Filter Set
open scoped BigOperators Topology

namespace PhasedElimination

theorem exists_ridge_design {k d T : Nat} (hd : 0 < d) (hT : 2 * d <= T)
    (arms : Fin k -> Fin d -> Real) (S : Finset (Fin k)) (hS : S.Nonempty)
    {e : Real} (he : 0 < e) :
    ∃ (schedule : Fin T -> Fin k) (weights : Fin k -> Fin T -> Real),
      (forall t, schedule t ∈ S) ∧
      (forall j, ∑ t, (weights j t)^2 <= 2 * (d : Real) / T) ∧
      (∀ j ∈ S, forall q,
        ((∑ t, weights j t * arms (schedule t) q) - arms j q)^2 <=
          e * (2 * (d : Real) / T)) := by
  classical
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨s, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin T -> S))
    (fun s => (ridge e (fun t => arms (s t))).det) Finset.univ_nonempty
  let x := fun t => arms (s t)
  have hv (j : Fin k) (hj : j ∈ S) :
      arms j ⬝ᵥ (ridge e x)⁻¹ *ᵥ arms j <= 2 * (d : Real) / T := by
    apply ridge_leverage_bound hd hT he
    intro t
    have h := hmax (Function.update s t ⟨j, hj⟩) (Finset.mem_univ _)
    have hx : (fun u => arms (Function.update s t ⟨j, hj⟩ u)) =
        Function.update x t (arms j) := by
      exact Function.comp_update (fun a : S => arms a) s t ⟨j, hj⟩
    simpa only [hx] using h
  let weights := fun j t => if j ∈ S then x t ⬝ᵥ (ridge e x)⁻¹ *ᵥ arms j else 0
  refine ⟨fun t => s t, weights, fun t => (s t).property, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · simpa only [weights, if_pos hj] using (ridge_weights_bounds he x (arms j) (hv j hj)).1
    · simp only [weights, if_neg hj, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
      positivity
  · intro j hj q
    simpa only [weights, if_pos hj] using (ridge_weights_bounds he x (arms j) (hv j hj)).2 q

/-- An exact integer schedule represents every active arm with uniformly bounded squared weights.
No assumption on the rank of the active arms is required. -/
theorem exists_exact_design {k d T : Nat} (hd : 0 < d) (hT : 2 * d <= T)
    (arms : Fin k -> Fin d -> Real) (S : Finset (Fin k)) (hS : S.Nonempty) :
    ∃ (schedule : Fin T -> Fin k) (weights : Fin k -> Fin T -> Real),
      (forall t, schedule t ∈ S) ∧
      (∀ j ∈ S, forall q, ∑ t, weights j t * arms (schedule t) q = arms j q) ∧
      (forall j, ∑ t, (weights j t)^2 <= 2 * (d : Real) / T) := by
  classical
  let C : Real := 2 * (d : Real) / T
  have hC : 0 <= C := by dsimp [C]; positivity
  let e : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have he (n : Nat) : 0 < e n := by dsimp [e]; positivity
  have hezero : Tendsto e atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose s w hs hw herr using fun n => exists_ridge_design hd hT arms S hS (he n)
  have hbox (n : Nat) : w n ∈ Icc (fun _ _ => -Real.sqrt C) (fun _ _ => Real.sqrt C) := by
    constructor <;> intro j t
    all_goals
      have hsq : (w n j t)^2 <= C :=
        (Finset.single_le_sum (fun u (_ : u ∈ Finset.univ) => sq_nonneg (w n j u))
          (Finset.mem_univ t)).trans (hw n j)
    · have h := Real.le_sqrt_of_sq_le (by simpa only [neg_sq] using hsq : (-w n j t)^2 <= C)
      linarith
    · exact Real.le_sqrt_of_sq_le hsq
  obtain ⟨weights, _, phi, hphi, hweights⟩ :=
    (isCompact_Icc : IsCompact (Icc (fun _ : Fin k => fun _ : Fin T => -Real.sqrt C)
      (fun _ _ => Real.sqrt C))).tendsto_subseq hbox
  have hfreq : ∃ schedule : Fin T -> Fin k, ∃ᶠ n : Nat in atTop, s (phi n) = schedule := by
    apply Filter.frequently_exists.mp
    exact Filter.Frequently.of_forall fun n => ⟨s (phi n), rfl⟩
  obtain ⟨schedule, hschedule⟩ := hfreq
  obtain ⟨psi, hpsi, hschedule⟩ := Filter.exists_seq_forall_of_frequently hschedule
  let seq := phi ∘ psi
  have hseq : Tendsto seq atTop atTop := hphi.tendsto_atTop.comp hpsi
  have hwlim : Tendsto (w ∘ seq) atTop (nhds weights) := hweights.comp hpsi
  have hwpoint (j : Fin k) (t : Fin T) :
      Tendsto (fun n => w (seq n) j t) atTop (nhds (weights j t)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hwlim j) t
  have hsseq (n : Nat) : s (seq n) = schedule := hschedule n
  refine ⟨schedule, weights, ?_, ?_, ?_⟩
  · intro t
    rw [← hsseq 0]
    exact hs (seq 0) t
  · intro j hj q
    have hconv : Tendsto (fun n => ((∑ t, w (seq n) j t * arms (schedule t) q) - arms j q)^2)
        atTop (nhds (((∑ t, weights j t * arms (schedule t) q) - arms j q)^2)) := by
      exact ((tendsto_finsetSum _ fun t _ => (hwpoint j t).mul_const _).sub_const _).pow 2
    have hzero : Tendsto (fun n => e (seq n) * C) atTop (nhds 0) := by
      simpa only [Function.comp_apply, zero_mul] using (hezero.comp hseq).mul_const C
    have hle : ((∑ t, weights j t * arms (schedule t) q) - arms j q)^2 <= 0 := by
      apply le_of_tendsto_of_tendsto hconv hzero
      exact Eventually.of_forall fun n => by simpa only [hsseq n] using herr (seq n) j hj q
    nlinarith [sq_nonneg ((∑ t, weights j t * arms (schedule t) q) - arms j q)]
  · intro j
    have hconv : Tendsto (fun n => ∑ t, (w (seq n) j t)^2) atTop
        (nhds (∑ t, (weights j t)^2)) :=
      tendsto_finsetSum _ fun t _ => (hwpoint j t).pow 2
    exact le_of_tendsto hconv (Eventually.of_forall fun n => hw (seq n) j)

end PhasedElimination
end

/- Complete adapted prior component: PhasePolicyCore. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators

namespace PhasedElimination

abbrev ActiveState (k : ℕ) := Fin k → Bool

def activeSet {k : ℕ} (A : ActiveState k) : Finset (Fin k) :=
  Finset.univ.filter (fun j ↦ A j = true)

@[simp] theorem mem_activeSet {k : ℕ} (A : ActiveState k) (j : Fin k) :
    j ∈ activeSet A ↔ A j = true := by simp [activeSet]

noncomputable def updateActive {k : ℕ} (A : ActiveState k) (e : Fin k → ℝ)
    (ε : ℝ) : ActiveState k := by
  classical
  exact fun j ↦ if A j = true ∧ ∀ a, A a = true → e a ≤ e j + 2 * ε then true else false

@[simp] theorem updateActive_eq_true {k : ℕ} (A : ActiveState k)
    (e : Fin k → ℝ) (ε : ℝ) (j : Fin k) :
    updateActive A e ε j = true ↔
      A j = true ∧ ∀ a, A a = true → e a ≤ e j + 2 * ε := by
  classical
  simp [updateActive]

theorem updateActive_subset {k : ℕ} (A : ActiveState k) (e : Fin k → ℝ) (ε : ℝ) :
    activeSet (updateActive A e ε) ⊆ activeSet A := by
  intro j hj
  exact (mem_activeSet _ _).2
    (((updateActive_eq_true A e ε j).1 ((mem_activeSet _ _).1 hj)).1)

theorem updateActive_nonempty {k : ℕ} {A : ActiveState k}
    (hA : (activeSet A).Nonempty) (e : Fin k → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (activeSet (updateActive A e ε)).Nonempty := by
  classical
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (activeSet A) e hA
  refine ⟨j, (mem_activeSet _ _).2 ((updateActive_eq_true _ _ _ _).2 ⟨?_, ?_⟩)⟩
  · exact (mem_activeSet _ _).1 hj
  · intro a ha
    exact (hmax a ((mem_activeSet _ _).2 ha)).trans (by linarith)

theorem updateActive_retains_best {k : ℕ} {A : ActiveState k}
    {μ e : Fin k → ℝ} {ε : ℝ} {best : Fin k}
    (hbest : A best = true) (hmax : ∀ a, μ a ≤ μ best)
    (haccuracy : ∀ a, A a = true → |e a - μ a| ≤ ε) :
    updateActive A e ε best = true := by
  apply (updateActive_eq_true _ _ _ _).2
  refine ⟨hbest, ?_⟩
  intro a ha
  have ha' := (abs_le.mp (haccuracy a ha)).2
  have hb' := (abs_le.mp (haccuracy best hbest)).1
  have hm := hmax a
  linarith

theorem updateActive_gap {k : ℕ} {A : ActiveState k}
    {μ e : Fin k → ℝ} {ε : ℝ} {best j : Fin k}
    (hbest : A best = true)
    (haccuracy : ∀ a, A a = true → |e a - μ a| ≤ ε)
    (hj : updateActive A e ε j = true) : μ best - μ j ≤ 4 * ε := by
  obtain ⟨hjA, hj⟩ := (updateActive_eq_true _ _ _ _).1 hj
  have he := hj best hbest
  have hb := (abs_le.mp (haccuracy best hbest)).1
  have ha := (abs_le.mp (haccuracy j hjA)).2
  linarith

theorem measurable_updateActive {k : ℕ} (ε : ℝ) :
    Measurable (fun p : ActiveState k × (Fin k → ℝ) ↦ updateActive p.1 p.2 ε) := by
  classical
  rw [measurable_pi_iff]
  intro j
  have hA (a : Fin k) : MeasurableSet {p : ActiveState k × (Fin k → ℝ) | p.1 a = true} :=
    measurableSet_eq_fun ((measurable_pi_apply a).comp measurable_fst) measurable_const
  have hE (a : Fin k) : MeasurableSet
      {p : ActiveState k × (Fin k → ℝ) | p.2 a ≤ p.2 j + 2 * ε} :=
    measurableSet_le ((measurable_pi_apply a).comp measurable_snd)
      (((measurable_pi_apply j).comp measurable_snd).add_const _)
  have hP : MeasurableSet {p : ActiveState k × (Fin k → ℝ) |
      p.1 j = true ∧ ∀ a, p.1 a = true → p.2 a ≤ p.2 j + 2 * ε} := by
    apply (hA j).inter
    change MeasurableSet {p : ActiveState k × (Fin k → ℝ) |
      ∀ a, p.1 a = true → p.2 a ≤ p.2 j + 2 * ε}
    have heq : {p : ActiveState k × (Fin k → ℝ) |
        ∀ a, p.1 a = true → p.2 a ≤ p.2 j + 2 * ε} =
        ⋂ a, {p | p.1 a = true}ᶜ ∪ {p | p.2 a ≤ p.2 j + 2 * ε} := by
      ext p
      simp [imp_iff_not_or]
    rw [heq]
    exact MeasurableSet.iInter (fun a ↦ (hA a).compl.union (hE a))
  exact measurable_const.ite hP measurable_const

structure PhasePlan (k M : ℕ) where
  schedule : (l : ℕ) → ActiveState k → Fin (phaseLength M l) → Fin k
  weights : (l : ℕ) → ActiveState k → Fin k → Fin (phaseLength M l) → ℝ

def policyPrefix {k n t : ℕ} (ht : t ≤ n) (h : BanditHistory k n) : BanditHistory k t :=
  fun i ↦ h (i.castLE ht)

theorem measurable_policyPrefix {k n t : ℕ} (ht : t ≤ n) :
    Measurable (policyPrefix (k := k) ht) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply _

@[simp] theorem policyPrefix_prefix {k n t s : ℕ} (hs : s ≤ t) (ht : t ≤ n)
    (h : BanditHistory k n) :
    policyPrefix hs (policyPrefix ht h) = policyPrefix (hs.trans ht) h := rfl

noncomputable def phaseEstimate {k M : ℕ} (p : PhasePlan k M) (l : ℕ)
    (A : ActiveState k) (h : BanditHistory k (phaseStart M (l + 1))) (j : Fin k) : ℝ :=
  ∑ t : Fin (phaseLength M l), p.weights l A j t *
    (h ⟨phaseStart M l + t, by rw [phaseStart_succ]; omega⟩).2

theorem measurable_phaseEstimate {k M : ℕ} (p : PhasePlan k M) (l : ℕ) :
    Measurable (fun q : ActiveState k × BanditHistory k (phaseStart M (l + 1)) ↦
      phaseEstimate p l q.1 q.2) := by
  rw [measurable_pi_iff]
  intro j
  apply Finset.measurable_sum
  intro t _
  exact ((measurable_of_countable (fun A ↦ p.weights l A j t)).comp measurable_fst).mul
    (measurable_snd.comp ((measurable_pi_apply _).comp measurable_snd))

noncomputable def phaseState {k M : ℕ} (p : PhasePlan k M) :
    (l : ℕ) → BanditHistory k (phaseStart M l) → ActiveState k
  | 0, _ => fun _ ↦ true
  | l + 1, h =>
      let A := phaseState p l (policyPrefix (phaseStart_mono M (Nat.le_succ l)) h)
      updateActive A (phaseEstimate p l A h) (phaseRadius l)

theorem measurable_phaseState {k M : ℕ} (p : PhasePlan k M) (l : ℕ) :
    Measurable (phaseState p l) := by
  induction l with
  | zero => exact measurable_const
  | succ l ih =>
      have hA := ih.comp (measurable_policyPrefix (phaseStart_mono M (Nat.le_succ l)))
      exact (measurable_updateActive (phaseRadius l)).comp
        (hA.prodMk ((measurable_phaseEstimate p l).comp (hA.prodMk measurable_id)))

theorem phaseState_nonempty {k M : ℕ} (hk : 0 < k) (p : PhasePlan k M) (l : ℕ)
    (h : BanditHistory k (phaseStart M l)) : (activeSet (phaseState p l h)).Nonempty := by
  induction l with
  | zero => exact ⟨⟨0, hk⟩, by simp [phaseState]⟩
  | succ l ih =>
      apply updateActive_nonempty (ih _) _
      exact pow_nonneg (by norm_num) _

theorem exists_phase {M : ℕ} (hM : 0 < M) (t : ℕ) :
    ∃ l, t < phaseStart M (l + 1) := by
  exact ⟨Nat.clog 2 (t + 1), lt_of_lt_of_le (Nat.lt_succ_self t) (phaseStart_covers hM)⟩

noncomputable def phaseIndex {M : ℕ} (hM : 0 < M) (t : ℕ) : ℕ := Nat.find (exists_phase hM t)

theorem phaseIndex_spec {M : ℕ} (hM : 0 < M) (t : ℕ) :
    phaseStart M (phaseIndex hM t) ≤ t ∧ t < phaseStart M (phaseIndex hM t + 1) := by
  refine ⟨?_, Nat.find_spec (exists_phase hM t)⟩
  cases h : phaseIndex hM t with
  | zero => simp [phaseStart_zero]
  | succ q =>
      have hmin := Nat.find_min (exists_phase hM t) (show q < phaseIndex hM t by omega)
      omega

theorem phaseIndex_eq {M : ℕ} (hM : 0 < M) {t l : ℕ}
    (hlo : phaseStart M l ≤ t) (hhi : t < phaseStart M (l + 1)) : phaseIndex hM t = l := by
  have hle : phaseIndex hM t ≤ l := Nat.find_min' (exists_phase hM t) hhi
  by_contra hne
  have hlt : phaseIndex hM t + 1 ≤ l := by omega
  have hm := phaseStart_mono M hlt
  have hu := (phaseIndex_spec hM t).2
  omega

noncomputable def phaseChoose {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (t : ℕ) (h : BanditHistory k t) : Fin k :=
  let l := phaseIndex hM t
  let A := phaseState p l (policyPrefix (phaseIndex_spec hM t).1 h)
  p.schedule l A ⟨t - phaseStart M l, by
    change t - phaseStart M (phaseIndex hM t) < phaseLength M (phaseIndex hM t)
    have hs := phaseIndex_spec hM t
    rw [phaseStart_succ] at hs
    omega⟩

theorem measurable_phaseChoose {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M) (t : ℕ) :
    Measurable (phaseChoose hM p t) := by
  exact (measurable_of_countable (fun A : ActiveState k ↦ p.schedule _ A _)).comp
    ((measurable_phaseState p _).comp (measurable_policyPrefix (phaseIndex_spec hM t).1))

noncomputable def phasePolicy {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M) : BanditPolicy k where
  select t := Kernel.deterministic (phaseChoose hM p t) (measurable_phaseChoose hM p t)
  markov _ := inferInstance

end PhasedElimination
end

/- Complete adapted prior component: PhasePolicyTrace. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators

namespace PhasedElimination

theorem policyPrefix_snoc {k n t : ℕ} (ht : t ≤ n)
    (h : BanditHistory k n) (q : Fin k × ℝ) :
    policyPrefix (ht.trans (Nat.le_succ n)) (Fin.snoc h q) = policyPrefix ht h := by
  funext i
  simp [policyPrefix, Fin.snoc, show (i : ℕ) < n by omega]
  exact congrArg h (Fin.ext rfl)

theorem policyPrefix_snoc_last {k n : ℕ} (h : BanditHistory k n) (q : Fin k × ℝ) :
    policyPrefix (Nat.le_succ n) (Fin.snoc h q) = h := by
  funext i
  simp [policyPrefix, Fin.snoc, i.isLt]
  exact congrArg h (Fin.ext rfl)

def PolicyFollows {k M n : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (h : BanditHistory k n) : Prop :=
  ∀ t : Fin n, (h t).1 = phaseChoose hM p t (policyPrefix t.isLt.le h)

theorem measurableSet_policyFollows {k M n : ℕ} (hM : 0 < M) (p : PhasePlan k M) :
    MeasurableSet {h : BanditHistory k n | PolicyFollows hM p h} := by
  simp only [PolicyFollows, Set.setOf_forall]
  exact MeasurableSet.iInter fun t ↦ measurableSet_eq_fun (measurable_pi_apply t).fst
    ((measurable_phaseChoose hM p t).comp (measurable_policyPrefix t.isLt.le))

theorem policyFollows_snoc_iff {k M n : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (h : BanditHistory k n) (q : Fin k × ℝ) :
    PolicyFollows hM p (Fin.snoc h q) ↔
      PolicyFollows hM p h ∧ q.1 = phaseChoose hM p n h := by
  constructor
  · intro hf
    constructor
    · intro t
      have ht := hf t.castSucc
      simpa only [Fin.val_castSucc, Fin.snoc_castSucc, policyPrefix_snoc t.isLt.le h q] using ht
    · have ht := hf (Fin.last n)
      simpa only [Fin.val_last, Fin.snoc_last, policyPrefix_snoc_last] using ht
  · rintro ⟨hf, hq⟩ t
    refine Fin.lastCases ?_ (fun i ↦ ?_) t
    · simpa only [Fin.val_last, Fin.snoc_last, policyPrefix_snoc_last] using hq
    · simpa only [Fin.val_castSucc, Fin.snoc_castSucc, policyPrefix_snoc i.isLt.le h q] using hf i

theorem ae_step_phaseChoose {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (ν : StochasticBandit k) (t : ℕ) (h : BanditHistory k t) :
    ∀ᵐ q ∂banditStepKernel ν (phasePolicy hM p) t h,
      q.1 = phaseChoose hM p t h := by
  have hselect : ∀ᵐ j ∂(phasePolicy hM p).select t h,
      j = phaseChoose hM p t h := by
    simp [phasePolicy, Kernel.deterministic_apply]
  unfold banditStepKernel
  refine Kernel.ae_compProd_of_ae_ae
    (measurableSet_eq_fun measurable_fst measurable_const) ?_
  filter_upwards [hselect] with j hj
  exact Filter.Eventually.of_forall fun _ ↦ hj

theorem ae_policyFollows {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (ν : StochasticBandit k) (n : ℕ) :
    ∀ᵐ h ∂banditMeasure ν (phasePolicy hM p) n, PolicyFollows hM p h := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun h t ↦ t.elim0
  | succ n ih =>
      rw [banditMeasure, ae_map_iff measurable_banditHistorySnoc.aemeasurable
        (measurableSet_policyFollows hM p)]
      refine Measure.ae_compProd_of_ae_ae
        ((measurableSet_policyFollows hM p).preimage measurable_banditHistorySnoc) ?_
      filter_upwards [ih] with h hh
      filter_upwards [ae_step_phaseChoose hM p ν n h] with q hq
      exact (policyFollows_snoc_iff hM p h q).2 ⟨hh, hq⟩

theorem phaseChoose_in_block {k M : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (l : ℕ) (t : Fin (phaseLength M l))
    (h : BanditHistory k (phaseStart M l + t)) :
    phaseChoose hM p (phaseStart M l + t) h =
      p.schedule l (phaseState p l (policyPrefix (Nat.le_add_right _ _) h)) t := by
  have hi : phaseIndex hM (phaseStart M l + t) = l := by
    apply phaseIndex_eq hM (Nat.le_add_right _ _)
    rw [phaseStart_succ]
    exact Nat.add_lt_add_left t.isLt _
  have aux (q : ℕ) (hq : q = l)
      (hb : phaseStart M q ≤ phaseStart M l + t)
      (hb' : phaseStart M l + t - phaseStart M q < phaseLength M q) :
      p.schedule q (phaseState p q (policyPrefix hb h))
          ⟨phaseStart M l + t - phaseStart M q, hb'⟩ =
        p.schedule l (phaseState p l (policyPrefix (Nat.le_add_right _ _) h)) t := by
    subst q
    congr 1
    exact Fin.ext (Nat.add_sub_cancel_left _ _)
  exact aux _ hi _ _

theorem recorded_schedule_of_follows {k M n : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (h : BanditHistory k n) (hf : PolicyFollows hM p h) (l : ℕ)
    (hn : phaseStart M l + phaseLength M l ≤ n) (t : Fin (phaseLength M l)) :
    (h ⟨phaseStart M l + t, by omega⟩).1 =
      p.schedule l (phaseState p l (policyPrefix (by omega) h)) t := by
  have hr := hf ⟨phaseStart M l + t, by omega⟩
  rw [phaseChoose_in_block] at hr
  simpa only [policyPrefix_prefix] using hr

theorem ae_recorded_schedule {k M n : ℕ} (hM : 0 < M) (p : PhasePlan k M)
    (ν : StochasticBandit k) (l : ℕ) (hn : phaseStart M l + phaseLength M l ≤ n) :
    ∀ᵐ h ∂banditMeasure ν (phasePolicy hM p) n,
      ∀ t : Fin (phaseLength M l),
        (h ⟨phaseStart M l + t, by omega⟩).1 =
          p.schedule l (phaseState p l (policyPrefix (by omega) h)) t := by
  filter_upwards [ae_policyFollows hM p ν n] with h hh
  exact recorded_schedule_of_follows hM p h hh l hn

end PhasedElimination
end

/- Complete adapted prior component: PhaseDesignPlan. -/
section
open Matrix
open scoped BigOperators

namespace PhasedElimination

theorem phaseLength_ge_base (M l : Nat) : M <= phaseLength M l := by
  have hp : 1 <= 4^l := Nat.succ_le_of_lt (pow_pos (by decide) l)
  simpa only [phaseLength, Nat.mul_one] using Nat.mul_le_mul_left M hp

noncomputable def exactPhasePlan {k d M : Nat} (hk : 0 < k) (hd : 0 < d)
    (hM : 2 * d <= M) (arms : Fin k -> Fin d -> Real) : PhasePlan k M := by
  classical
  exact {
    schedule := fun l A =>
      if hA : (activeSet A).Nonempty then
        (exists_exact_design hd (hM.trans (phaseLength_ge_base M l)) arms (activeSet A) hA).choose
      else fun _ => ⟨0, hk⟩
    weights := fun l A =>
      if hA : (activeSet A).Nonempty then
        (exists_exact_design hd (hM.trans (phaseLength_ge_base M l)) arms (activeSet A)
          hA).choose_spec.choose
      else fun _ _ => 0 }

theorem exactPhasePlan_schedule_supported {k d M : Nat}
    (hk : 0 < k) (hd : 0 < d) (hM : 2 * d <= M)
    (arms : Fin k -> Fin d -> Real) (l : Nat) (A : ActiveState k)
    (hA : (activeSet A).Nonempty) (t : Fin (phaseLength M l)) :
    (exactPhasePlan hk hd hM arms).schedule l A t ∈ activeSet A := by
  classical
  simpa only [exactPhasePlan, dif_pos hA] using
    (exists_exact_design hd (hM.trans (phaseLength_ge_base M l)) arms (activeSet A)
      hA).choose_spec.choose_spec.1 t

theorem exactPhasePlan_representation {k d M : Nat}
    (hk : 0 < k) (hd : 0 < d) (hM : 2 * d <= M)
    (arms : Fin k -> Fin d -> Real) (l : Nat) (A : ActiveState k)
    (j : Fin k) (hj : j ∈ activeSet A) (q : Fin d) :
    ∑ t, (exactPhasePlan hk hd hM arms).weights l A j t *
      arms ((exactPhasePlan hk hd hM arms).schedule l A t) q = arms j q := by
  classical
  have hA : (activeSet A).Nonempty := ⟨j, hj⟩
  simpa only [exactPhasePlan, dif_pos hA] using
    (exists_exact_design hd (hM.trans (phaseLength_ge_base M l)) arms (activeSet A)
      hA).choose_spec.choose_spec.2.1 j hj q

theorem exactPhasePlan_weight_sq_sum {k d M : Nat}
    (hk : 0 < k) (hd : 0 < d) (hM : 2 * d <= M)
    (arms : Fin k -> Fin d -> Real) (l : Nat) (A : ActiveState k) (j : Fin k) :
    ∑ t, ((exactPhasePlan hk hd hM arms).weights l A j t)^2 <=
      2 * (d : Real) / phaseLength M l := by
  classical
  by_cases hA : (activeSet A).Nonempty
  · simpa only [exactPhasePlan, dif_pos hA] using
      (exists_exact_design hd (hM.trans (phaseLength_ge_base M l)) arms (activeSet A)
        hA).choose_spec.choose_spec.2.2 j
  · simp only [exactPhasePlan, dif_neg hA, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

theorem exactPhasePlan_weighted_mean_eq {k d M : Nat}
    (hk : 0 < k) (hd : 0 < d) (hM : 2 * d <= M)
    (arms : Fin k -> Fin d -> Real) (theta : Fin d -> Real) (mean : Fin k -> Real)
    (hmean : forall a, mean a = arms a ⬝ᵥ theta)
    (l : Nat) (A : ActiveState k) (j : Fin k) (hj : j ∈ activeSet A) :
    ∑ t, (exactPhasePlan hk hd hM arms).weights l A j t *
      mean ((exactPhasePlan hk hd hM arms).schedule l A t) = mean j := by
  simp_rw [hmean, dotProduct, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, exactPhasePlan_representation hk hd hM arms l A j hj]

end PhasedElimination
end

/- Complete adapted prior component: PhaseConcentrationCore. -/
section
/-!
Predictable scalar concentration under the canonical bandit law.

The one-step integration and score induction adapt the public complete proof
of BanditAlgorithm.bandit_adaptive_stopped_exp_score_lintegral_le_one,
theorem 3a6d8240-8f4a-4068-8024-43ef6a7dc52e, accepted submission
e9055989-9df6-48cb-86a2-ffa95c037236, SHA256
4005a2eae74323c156f0569c504f0cff82c2cdac767f1e6649b6c8446034e53a.
Here an arbitrary measurable predictable coefficient replaces its stopped
arm indicator. Prefix identities also follow the locally verified
ContinuousLinUCB.CanonicalHistory component (424d601b...). No theorem from
the target itself is imported. The model is subgaussian, not Gaussian.
-/

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace PhasedElimination

def phaseHistoryPrefix {k n : ℕ} (t : ℕ) (ht : t ≤ n)
    (h : BanditHistory k n) : BanditHistory k t := fun i => h (i.castLE ht)

theorem measurable_phaseHistoryPrefix {k n : ℕ} (t : ℕ) (ht : t ≤ n) :
    Measurable (phaseHistoryPrefix (k := k) t ht) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

theorem phaseHistoryPrefix_snoc {k n t : ℕ} (ht : t ≤ n)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    phaseHistoryPrefix t (ht.trans (Nat.le_succ n)) (Fin.snoc h z) =
      phaseHistoryPrefix t ht h := by
  funext i
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt ht
  simp [phaseHistoryPrefix, Fin.snoc, hi]
  congr 1

theorem phaseHistoryPrefix_snoc_last {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    phaseHistoryPrefix n (Nat.le_succ n) (Fin.snoc h z) = h := by
  funext i
  simp [phaseHistoryPrefix, Fin.snoc, i.isLt]
  congr 1

abbrev PredictableScalar (k : ℕ) :=
  (m : ℕ) → BanditHistory k m → Fin k → ℝ

def MeasurablePredictableScalar {k : ℕ} (b : PredictableScalar k) : Prop :=
  ∀ m, Measurable (fun p : BanditHistory k m × Fin k => b m p.1 p.2)

noncomputable def weightedCenteredSum {k : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (n : ℕ) (h : BanditHistory k n) : ℝ :=
  ∑ t : Fin n, b t.val (phaseHistoryPrefix t.val (Nat.le_of_lt t.isLt) h) (h t).1 *
    ((h t).2 - banditArmMean nu (h t).1)

noncomputable def weightedEnergy {k : ℕ} (b : PredictableScalar k)
    (n : ℕ) (h : BanditHistory k n) : ℝ :=
  ∑ t : Fin n, (b t.val (phaseHistoryPrefix t.val (Nat.le_of_lt t.isLt) h) (h t).1) ^ 2

theorem weightedCenteredSum_snoc {k n : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    weightedCenteredSum nu b (n + 1) (Fin.snoc h z) =
      weightedCenteredSum nu b n h + b n h z.1 * (z.2 - banditArmMean nu z.1) := by
  simp only [weightedCenteredSum, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    rw [phaseHistoryPrefix_snoc]
  · simp only [Fin.val_last, Fin.snoc_last, phaseHistoryPrefix_snoc_last]

theorem weightedEnergy_snoc {k n : ℕ} (b : PredictableScalar k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    weightedEnergy b (n + 1) (Fin.snoc h z) =
      weightedEnergy b n h + (b n h z.1) ^ 2 := by
  simp only [weightedEnergy, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    rw [phaseHistoryPrefix_snoc]
  · simp only [Fin.val_last, Fin.snoc_last, phaseHistoryPrefix_snoc_last]

theorem measurable_weightedCenteredSum {k n : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) :
    Measurable (weightedCenteredSum nu b n) := by
  apply Finset.measurable_sum
  intro t _
  have hc := (hb t.val).comp ((measurable_phaseHistoryPrefix t.val
    (Nat.le_of_lt t.isLt)).prodMk (measurable_fst.comp (measurable_pi_apply t)))
  have hm : Measurable (banditArmMean nu) := measurable_of_countable _
  exact hc.mul ((measurable_snd.comp (measurable_pi_apply t)).sub
    (hm.comp (measurable_fst.comp (measurable_pi_apply t))))

theorem measurable_weightedEnergy {k n : ℕ} (b : PredictableScalar k)
    (hb : MeasurablePredictableScalar b) : Measurable (weightedEnergy b n) := by
  apply Finset.measurable_sum
  intro t _
  exact ((hb t.val).comp ((measurable_phaseHistoryPrefix t.val
    (Nat.le_of_lt t.isLt)).prodMk
      (measurable_fst.comp (measurable_pi_apply t)))).pow_const 2

noncomputable def weightedExpScore {k : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (lam : ℝ) (n : ℕ) (h : BanditHistory k n) : ℝ :=
  Real.exp (lam * weightedCenteredSum nu b n h - lam ^ 2 / 2 * weightedEnergy b n h)

theorem measurable_weightedExpScore {k n : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ) :
    Measurable (weightedExpScore nu b lam n) :=
  ((measurable_const.mul (measurable_weightedCenteredSum nu b hb)).sub
    (measurable_const.mul (measurable_weightedEnergy b hb))).exp

noncomputable def weightedScoreFactor {k m : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (lam : ℝ) (p : BanditHistory k m × (Fin k × ℝ)) : ℝ :=
  Real.exp (lam * b m p.1 p.2.1 * (p.2.2 - banditArmMean nu p.2.1) -
    (lam * b m p.1 p.2.1) ^ 2 / 2)

theorem measurable_weightedScoreFactor {k m : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ) :
    Measurable (weightedScoreFactor (m := m) nu b lam) := by
  have hc : Measurable (fun p : BanditHistory k m × (Fin k × ℝ) => b m p.1 p.2.1) :=
    (hb m).comp (measurable_fst.prodMk measurable_snd.fst)
  have hm : Measurable (banditArmMean nu) := measurable_of_countable _
  exact (((measurable_const.mul hc).mul
    (measurable_snd.snd.sub (hm.comp measurable_snd.fst))).sub
      (((measurable_const.mul hc).pow_const 2).div_const 2)).exp

theorem weightedExpScore_snoc {k m : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (lam : ℝ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    weightedExpScore nu b lam (m + 1) (Fin.snoc h z) =
      weightedExpScore nu b lam m h * weightedScoreFactor nu b lam (h, z) := by
  rw [weightedExpScore, weightedCenteredSum_snoc, weightedEnergy_snoc,
    weightedExpScore, weightedScoreFactor, ← Real.exp_add]
  congr 1
  ring

theorem integrable_weightedScoreFactor_step {k m : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ)
    (h : BanditHistory k m) :
    Integrable (fun z => weightedScoreFactor nu b lam (h, z)) (banditStepKernel nu pi m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_weightedScoreFactor nu b hb lam).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    rw [show (banditRewardKernel nu) a = nu.P a by
      simp [banditRewardKernel, Kernel.ofFunOfCountable]]
    have hbase := (hnu.2 a).integrable_exp_mul (lam * b m h a) |>.mul_const
      (Real.exp (-((lam * b m h a) ^ 2 / 2)))
    convert hbase using 1
    funext y
    rw [← Real.exp_add]
    rfl
  · exact Integrable.of_finite

theorem weightedScoreFactor_step_integral_le_one {k m : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ)
    (h : BanditHistory k m) :
    (∫ z, weightedScoreFactor nu b lam (h, z) ∂banditStepKernel nu pi m h) ≤ 1 := by
  have hint := integrable_weightedScoreFactor_step nu hnu pi b hb lam h
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, weightedScoreFactor nu b lam (h, (a, y))
      ∂((banditRewardKernel nu).comap Prod.snd measurable_snd) (h, a)
      ∂pi.select m h) ≤ ∫ _a, (1 : ℝ) ∂pi.select m h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      rw [show (banditRewardKernel nu) a = nu.P a by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      have hm := (hnu.2 a).mgf_le (lam * b m h a)
      rw [mgf] at hm
      have hm' : (∫ y, Real.exp ((lam * b m h a) * (y - banditArmMean nu a))
          ∂nu.P a) ≤ Real.exp ((lam * b m h a) ^ 2 / 2) := by simpa using hm
      calc
        (∫ y, weightedScoreFactor nu b lam (h, (a, y)) ∂nu.P a) =
            Real.exp (-((lam * b m h a) ^ 2 / 2)) *
              ∫ y, Real.exp ((lam * b m h a) * (y - banditArmMean nu a)) ∂nu.P a := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          rw [weightedScoreFactor, ← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-((lam * b m h a) ^ 2 / 2)) *
            Real.exp ((lam * b m h a) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; simp
    _ = 1 := by simp

theorem integrable_weightedScore_product {k m : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ)
    (mu : Measure (BanditHistory k m)) [IsProbabilityMeasure mu]
    (hold : Integrable (weightedExpScore nu b lam m) mu) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) =>
      weightedExpScore nu b lam m p.1 * weightedScoreFactor nu b lam p)
      (mu.compProd (banditStepKernel nu pi m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p =>
    weightedExpScore nu b lam m p.1 * weightedScoreFactor nu b lam p
  have hG : StronglyMeasurable G :=
    (((measurable_weightedExpScore nu b hb lam).comp measurable_fst).mul
      (measurable_weightedScoreFactor nu b hb lam)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h =>
      (integrable_weightedScoreFactor_step nu hnu pi b hb lam h).const_mul
        (weightedExpScore nu b lam m h)
  · apply Integrable.mono hold hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards with h
    have hscore : 0 ≤ weightedExpScore nu b lam m h := Real.exp_nonneg _
    have hfactor : ∀ z, 0 ≤ weightedScoreFactor nu b lam (h, z) := fun _ => Real.exp_nonneg _
    have hinner : 0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel nu pi m h :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hinner]
    change (∫ z, ‖weightedExpScore nu b lam m h * weightedScoreFactor nu b lam (h, z)‖
      ∂banditStepKernel nu pi m h) ≤ ‖weightedExpScore nu b lam m h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore, abs_of_nonneg (hfactor _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore
      (weightedScoreFactor_step_integral_le_one nu hnu pi b hb lam h)

theorem weightedExpScore_integrable_and_integral_le_one {k : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b) (lam : ℝ) (n : ℕ) :
    Integrable (weightedExpScore nu b lam n) (banditMeasure nu pi n) ∧
      (∫ h, weightedExpScore nu b lam n h ∂banditMeasure nu pi n) ≤ 1 := by
  induction n with
  | zero => constructor <;> simp [weightedExpScore, weightedCenteredSum, weightedEnergy]
  | succ n ih =>
    let mu := banditMeasure nu pi n
    let kap := banditStepKernel nu pi n
    let snoc : BanditHistory k n × (Fin k × ℝ) → BanditHistory k (n + 1) :=
      fun p => Fin.snoc p.1 p.2
    let F : BanditHistory k n × (Fin k × ℝ) → ℝ := fun p =>
      weightedExpScore nu b lam n p.1 * weightedScoreFactor nu b lam p
    have heq : (fun p => weightedExpScore nu b lam (n + 1) (snoc p)) = F := by
      funext p
      exact weightedExpScore_snoc nu b lam p.1 p.2
    have hcomp : Integrable F (mu.compProd kap) :=
      integrable_weightedScore_product nu hnu pi b hb lam mu ih.1
    constructor
    · rw [banditMeasure]
      apply (integrable_map_measure (measurable_weightedExpScore
        (n := n + 1) nu b hb lam).aestronglyMeasurable
        measurable_banditHistorySnoc.aemeasurable).2
      change Integrable (fun p => weightedExpScore nu b lam (n + 1) (snoc p)) (mu.compProd kap)
      rw [heq]
      exact hcomp
    · rw [banditMeasure, integral_map measurable_banditHistorySnoc.aemeasurable
        (measurable_weightedExpScore (n := n + 1) nu b hb lam).aestronglyMeasurable]
      change (∫ p, weightedExpScore nu b lam (n + 1) (snoc p) ∂mu.compProd kap) ≤ 1
      rw [heq, Measure.integral_compProd hcomp]
      calc
        (∫ h, ∫ z, F (h, z) ∂kap h ∂mu) ≤
            ∫ h, weightedExpScore nu b lam n h ∂mu := by
          apply integral_mono_ae hcomp.integral_compProd ih.1
          filter_upwards with h
          change (∫ z, weightedExpScore nu b lam n h * weightedScoreFactor nu b lam (h, z)
            ∂kap h) ≤ weightedExpScore nu b lam n h
          rw [integral_const_mul]
          exact mul_le_of_le_one_right (Real.exp_nonneg _)
            (weightedScoreFactor_step_integral_le_one nu hnu pi b hb lam h)
        _ ≤ 1 := ih.2

theorem weightedCenteredSum_upper_tail {k n : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b)
    (v : ℝ) (hv : 0 < v) (henergy : ∀ h, weightedEnergy b n h ≤ v)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu pi n).real {h | eps ≤ weightedCenteredSum nu b n h} ≤
      Real.exp (-eps ^ 2 / (2 * v)) := by
  let lam := eps / v
  let X : BanditHistory k n → ℝ := fun h =>
    weightedCenteredSum nu b n h - lam / 2 * weightedEnergy b n h
  have hlam : 0 ≤ lam := div_nonneg heps hv.le
  have hscore := weightedExpScore_integrable_and_integral_le_one nu hnu pi b hb lam n
  have heq : (fun h => Real.exp (lam * X h)) = weightedExpScore nu b lam n := by
    funext h
    unfold X weightedExpScore
    congr 1
    ring
  have hint : Integrable (fun h => Real.exp (lam * X h)) (banditMeasure nu pi n) := by
    rw [heq]
    exact hscore.1
  have hchern := measure_ge_le_exp_mul_mgf (μ := banditMeasure nu pi n) (X := X)
    (eps / 2) hlam hint
  calc
    (banditMeasure nu pi n).real {h | eps ≤ weightedCenteredSum nu b n h} ≤
        (banditMeasure nu pi n).real {h | eps / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have he := henergy h
      have hm := mul_le_mul_of_nonneg_left he (div_nonneg hlam (by norm_num : (0 : ℝ) ≤ 2))
      have hvlam : lam * v = eps := by dsimp [lam]; field_simp
      dsimp [X]
      change eps ≤ weightedCenteredSum nu b n h at hh
      nlinarith
    _ ≤ Real.exp (-lam * (eps / 2)) * mgf X (banditMeasure nu pi n) lam := hchern
    _ ≤ Real.exp (-lam * (eps / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, heq]
        exact hscore.2
      · exact Real.exp_nonneg _
    _ = Real.exp (-eps ^ 2 / (2 * v)) := by
      rw [mul_one]
      congr 1
      dsimp [lam]
      field_simp

theorem weightedCenteredSum_neg {k n : ℕ} (nu : StochasticBandit k)
    (b : PredictableScalar k) (h : BanditHistory k n) :
    weightedCenteredSum nu (fun m p a => -b m p a) n h = -weightedCenteredSum nu b n h := by
  simp [weightedCenteredSum, Finset.sum_neg_distrib]

theorem weightedEnergy_neg {k n : ℕ} (b : PredictableScalar k) (h : BanditHistory k n) :
    weightedEnergy (fun m p a => -b m p a) n h = weightedEnergy b n h := by
  simp [weightedEnergy]

theorem weightedCenteredSum_lower_tail {k n : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b)
    (v : ℝ) (hv : 0 < v) (henergy : ∀ h, weightedEnergy b n h ≤ v)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu pi n).real {h | weightedCenteredSum nu b n h ≤ -eps} ≤
      Real.exp (-eps ^ 2 / (2 * v)) := by
  have hh := weightedCenteredSum_upper_tail nu hnu pi (fun m p a => -b m p a)
    (fun m => (hb m).neg) v hv (fun h => by rw [weightedEnergy_neg]; exact henergy h) eps heps
  convert hh using 1
  congr 1
  ext h
  simp only [Set.mem_setOf_eq, weightedCenteredSum_neg]
  constructor <;> intro hh <;> linarith

theorem weightedCenteredSum_abs_tail {k n : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b)
    (v : ℝ) (hv : 0 < v) (henergy : ∀ h, weightedEnergy b n h ≤ v)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu pi n).real {h | eps ≤ |weightedCenteredSum nu b n h|} ≤
      2 * Real.exp (-eps ^ 2 / (2 * v)) := by
  have heq : {h : BanditHistory k n | eps ≤ |weightedCenteredSum nu b n h|} =
      {h | eps ≤ weightedCenteredSum nu b n h} ∪
        {h | weightedCenteredSum nu b n h ≤ -eps} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
    constructor <;> intro hh
    · rcases hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by linarith)
    · rcases hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (by linarith)
  rw [heq]
  calc
    _ ≤ (banditMeasure nu pi n).real {h | eps ≤ weightedCenteredSum nu b n h} +
        (banditMeasure nu pi n).real {h | weightedCenteredSum nu b n h ≤ -eps} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-eps ^ 2 / (2 * v)) + Real.exp (-eps ^ 2 / (2 * v)) :=
      add_le_add (weightedCenteredSum_upper_tail nu hnu pi b hb v hv henergy eps heps)
        (weightedCenteredSum_lower_tail nu hnu pi b hb v hv henergy eps heps)
    _ = _ := by ring

theorem weightedCenteredSum_family_tail {k n : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : Fin k → PredictableScalar k) (hb : ∀ j, MeasurablePredictableScalar (b j))
    (v : ℝ) (hv : 0 < v) (henergy : ∀ j h, weightedEnergy (b j) n h ≤ v)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu pi n).real {h | ∃ j, eps < |weightedCenteredSum nu (b j) n h|} ≤
      2 * k * Real.exp (-eps ^ 2 / (2 * v)) := by
  calc
    _ ≤ (banditMeasure nu pi n).real
        (⋃ j : Fin k, {h | eps ≤ |weightedCenteredSum nu (b j) n h|}) := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      rintro h ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj.le⟩
    _ ≤ ∑ j : Fin k, (banditMeasure nu pi n).real
        {h | eps ≤ |weightedCenteredSum nu (b j) n h|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin k, 2 * Real.exp (-eps ^ 2 / (2 * v)) := by
      apply Finset.sum_le_sum
      intro j _
      exact weightedCenteredSum_abs_tail nu hnu pi (b j) (hb j) v hv (henergy j) eps heps
    _ = _ := by simp; ring

theorem weightedCenteredSum_subgaussian {k n : ℕ} (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (b : PredictableScalar k) (hb : MeasurablePredictableScalar b)
    (v : NNReal) (henergy : ∀ h, weightedEnergy b n h ≤ (v : ℝ)) :
    HasSubgaussianMGF (weightedCenteredSum nu b n) v (banditMeasure nu pi n) := by
  have major (lam : ℝ) (h : BanditHistory k n) :
      Real.exp (lam * weightedCenteredSum nu b n h) ≤
        Real.exp ((v : ℝ) * lam ^ 2 / 2) * weightedExpScore nu b lam n h := by
    rw [weightedExpScore, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (sub_nonneg.mpr (henergy h)) (sq_nonneg lam)
    nlinarith
  have hint (lam : ℝ) : Integrable (fun h => Real.exp (lam * weightedCenteredSum nu b n h))
      (banditMeasure nu pi n) := by
    have hscore := weightedExpScore_integrable_and_integral_le_one nu hnu pi b hb lam n
    apply Integrable.mono (hscore.1.const_mul (Real.exp ((v : ℝ) * lam ^ 2 / 2)))
      ((measurable_const.mul (measurable_weightedCenteredSum nu b hb)).exp.aestronglyMeasurable)
    filter_upwards with h
    have hnonneg : 0 ≤ weightedExpScore nu b lam n h := Real.exp_nonneg _
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) hnonneg)]
    exact major lam h
  refine ⟨hint, ?_⟩
  intro lam
  have hscore := weightedExpScore_integrable_and_integral_le_one nu hnu pi b hb lam n
  calc
    mgf (weightedCenteredSum nu b n) (banditMeasure nu pi n) lam ≤
        ∫ h, Real.exp ((v : ℝ) * lam ^ 2 / 2) * weightedExpScore nu b lam n h
          ∂banditMeasure nu pi n := by
      exact integral_mono_ae (hint lam) (hscore.1.const_mul _)
        (Filter.Eventually.of_forall (major lam))
    _ = Real.exp ((v : ℝ) * lam ^ 2 / 2) *
        ∫ h, weightedExpScore nu b lam n h ∂banditMeasure nu pi n := integral_const_mul _ _
    _ ≤ Real.exp ((v : ℝ) * lam ^ 2 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hscore.2 (Real.exp_nonneg _)
    _ = _ := mul_one _

end PhasedElimination
end

/- Complete adapted prior component: PhaseConcentrationBlock. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace PhasedElimination

theorem phaseHistoryPrefix_comp {k n t s : ℕ} (ht : t ≤ n) (hs : s ≤ t)
    (h : BanditHistory k n) :
    phaseHistoryPrefix s hs (phaseHistoryPrefix t ht h) =
      phaseHistoryPrefix s (hs.trans ht) h := by
  rfl

noncomputable def blockPredictable {k : ℕ} {State : Type*}
    (s T : ℕ) (state : BanditHistory k s → State) (w : State → Fin T → ℝ) :
    PredictableScalar k := fun m h _a =>
  if hm : s ≤ m ∧ m < s + T then
    w (state (phaseHistoryPrefix s hm.1 h)) ⟨m - s, by omega⟩
  else 0

theorem measurable_blockPredictable {k : ℕ} {State : Type*} [MeasurableSpace State]
    (s T : ℕ) (state : BanditHistory k s → State) (hs : Measurable state)
    (w : State → Fin T → ℝ) (hw : ∀ t, Measurable (fun z => w z t)) :
    MeasurablePredictableScalar (blockPredictable s T state w) := by
  intro m
  by_cases hm : s ≤ m ∧ m < s + T
  · have heq : (fun p : BanditHistory k m × Fin k => blockPredictable s T state w m p.1 p.2) =
        fun p => w (state (phaseHistoryPrefix s hm.1 p.1)) ⟨m - s, by omega⟩ := by
      funext p
      simp only [blockPredictable, dif_pos hm]
    rw [heq]
    exact (hw _).comp (hs.comp ((measurable_phaseHistoryPrefix s hm.1).comp measurable_fst))
  · have heq : (fun p : BanditHistory k m × Fin k => blockPredictable s T state w m p.1 p.2) =
        fun _ => 0 := by
      funext p
      simp only [blockPredictable, dif_neg hm]
    rw [heq]
    exact measurable_const

theorem blockPredictable_at {k n : ℕ} {State : Type*} (s T : ℕ)
    (state : BanditHistory k s → State) (w : State → Fin T → ℝ)
    (hs : s ≤ n) (h : BanditHistory k n) (t : Fin n) :
    blockPredictable s T state w t.val
        (phaseHistoryPrefix t.val (Nat.le_of_lt t.isLt) h) (h t).1 =
      if ht : s ≤ t.val ∧ t.val < s + T then
        w (state (phaseHistoryPrefix s hs h)) ⟨t.val - s, by omega⟩
      else 0 := by
  by_cases ht : s ≤ t.val ∧ t.val < s + T
  · simp only [blockPredictable, dif_pos ht]
    rw [phaseHistoryPrefix_comp]
  · simp only [blockPredictable, dif_neg ht]

theorem sum_consecutive {s T n : ℕ} (hn : s + T ≤ n) (f : Fin T → ℝ) :
    (∑ t : Fin n, if ht : s ≤ t.val ∧ t.val < s + T then f ⟨t.val - s, by omega⟩ else 0) =
      ∑ t : Fin T, f t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Fin.sum_univ_add]
  have htail : (∑ t : Fin u,
      if ht : s ≤ (Fin.natAdd (s + T) t).val ∧ (Fin.natAdd (s + T) t).val < s + T then
        f ⟨(Fin.natAdd (s + T) t).val - s, by omega⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have hnot : ¬(s ≤ (Fin.natAdd (s + T) t).val ∧
        (Fin.natAdd (s + T) t).val < s + T) := by simp only [Fin.val_natAdd]; omega
    rw [dif_neg hnot]
  rw [htail, add_zero, Fin.sum_univ_add]
  have hhead : (∑ t : Fin s,
      if ht : s ≤ (Fin.castAdd u (Fin.castAdd T t)).val ∧
          (Fin.castAdd u (Fin.castAdd T t)).val < s + T then
        f ⟨(Fin.castAdd u (Fin.castAdd T t)).val - s, by omega⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have hnot : ¬(s ≤ (Fin.castAdd u (Fin.castAdd T t)).val ∧
        (Fin.castAdd u (Fin.castAdd T t)).val < s + T) := by
      simp only [Fin.val_castAdd]
      omega
    rw [dif_neg hnot]
  rw [hhead, zero_add]
  apply Finset.sum_congr rfl
  intro t _
  have ht : s ≤ (Fin.castAdd u (Fin.natAdd s t)).val ∧
      (Fin.castAdd u (Fin.natAdd s t)).val < s + T := by
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  rw [dif_pos ht]
  congr 1
  apply Fin.ext
  simp

theorem sum_consecutive_of_eq {s T n : ℕ} (hn : s + T ≤ n)
    (F : Fin n → ℝ) (f : Fin T → ℝ)
    (hout : ∀ t, ¬(s ≤ t.val ∧ t.val < s + T) → F t = 0)
    (hin : ∀ t (ht : s ≤ t.val ∧ t.val < s + T), F t = f ⟨t.val - s, by omega⟩) :
    (∑ t : Fin n, F t) = ∑ t : Fin T, f t := by
  rw [← sum_consecutive hn f]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with ht
  · exact hin t ht
  · exact hout t ht

theorem weightedEnergy_block {k n : ℕ} {State : Type*} (s T : ℕ)
    (state : BanditHistory k s → State) (w : State → Fin T → ℝ)
    (hn : s + T ≤ n) (h : BanditHistory k n) :
    weightedEnergy (blockPredictable s T state w) n h =
      ∑ t : Fin T, (w (state (phaseHistoryPrefix s (by omega) h)) t) ^ 2 := by
  unfold weightedEnergy
  apply sum_consecutive_of_eq hn
  · intro t ht
    rw [blockPredictable_at s T state w (by omega), dif_neg ht]
    simp
  · intro t ht
    rw [blockPredictable_at s T state w (by omega), dif_pos ht]

def blockRound {s T n : ℕ} (hn : s + T ≤ n) (t : Fin T) : Fin n :=
  ⟨s + t.val, by omega⟩

noncomputable def blockCenteredSum {k n : ℕ} {State : Type*} (nu : StochasticBandit k)
    (s T : ℕ) (state : BanditHistory k s → State) (w : State → Fin T → ℝ)
    (hn : s + T ≤ n) (h : BanditHistory k n) : ℝ :=
  ∑ t : Fin T, w (state (phaseHistoryPrefix s (by omega) h)) t *
    ((h (blockRound hn t)).2 - banditArmMean nu (h (blockRound hn t)).1)

theorem weightedCenteredSum_block {k n : ℕ} {State : Type*} (nu : StochasticBandit k)
    (s T : ℕ) (state : BanditHistory k s → State) (w : State → Fin T → ℝ)
    (hn : s + T ≤ n) (h : BanditHistory k n) :
    weightedCenteredSum nu (blockPredictable s T state w) n h =
      blockCenteredSum nu s T state w hn h := by
  unfold weightedCenteredSum blockCenteredSum
  apply sum_consecutive_of_eq hn
  · intro t ht
    rw [blockPredictable_at s T state w (by omega), dif_neg ht]
    simp
  · intro t ht
    rw [blockPredictable_at s T state w (by omega), dif_pos ht]
    have hi : blockRound hn (⟨t.val - s, by omega⟩ : Fin T) = t := by
      apply Fin.ext
      simp only [blockRound]
      omega
    rw [hi]

theorem blockCenteredSum_family_tail {k n : ℕ} {State : Type*} [MeasurableSpace State]
    (nu : StochasticBandit k) (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (s T : ℕ) (hn : s + T ≤ n) (state : BanditHistory k s → State) (hs : Measurable state)
    (w : State → Fin k → Fin T → ℝ) (hw : ∀ j t, Measurable (fun z => w z j t))
    (v : ℝ) (hv : 0 < v) (hvar : ∀ z j, (∑ t : Fin T, (w z j t) ^ 2) ≤ v)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu pi n).real
      {h | ∃ j, eps < |blockCenteredSum nu s T state (fun z => w z j) hn h|} ≤
        2 * k * Real.exp (-eps ^ 2 / (2 * v)) := by
  have hh := weightedCenteredSum_family_tail nu hnu pi
    (fun j => blockPredictable s T state (fun z => w z j))
    (fun j => measurable_blockPredictable s T state hs (fun z => w z j) (hw j))
    v hv (fun j h => by rw [weightedEnergy_block s T state (fun z => w z j) hn]; exact hvar _ j)
    eps heps
  simpa only [weightedCenteredSum_block nu s T state _ hn] using hh

theorem blockCenteredSum_subgaussian {k n : ℕ} {State : Type*} [MeasurableSpace State]
    (nu : StochasticBandit k) (hnu : IsSubgaussianBandit 1 nu) (pi : BanditPolicy k)
    (s T : ℕ) (hn : s + T ≤ n) (state : BanditHistory k s → State) (hs : Measurable state)
    (w : State → Fin T → ℝ) (hw : ∀ t, Measurable (fun z => w z t))
    (v : NNReal) (hvar : ∀ z, (∑ t : Fin T, (w z t) ^ 2) ≤ (v : ℝ)) :
    HasSubgaussianMGF (blockCenteredSum nu s T state w hn) v (banditMeasure nu pi n) := by
  have hh := weightedCenteredSum_subgaussian nu hnu pi (blockPredictable s T state w)
    (measurable_blockPredictable s T state hs w hw) v
    (fun h => by rw [weightedEnergy_block s T state w hn]; exact hvar _)
  have heq : weightedCenteredSum nu (blockPredictable s T state w) n =
      blockCenteredSum nu s T state w hn := by
    funext h
    exact weightedCenteredSum_block nu s T state w hn h
  rwa [heq] at hh

noncomputable def blockEstimate {k n : ℕ} {State : Type*} (s T : ℕ)
    (state : BanditHistory k s → State) (w : State → Fin T → ℝ)
    (hn : s + T ≤ n) (h : BanditHistory k n) : ℝ :=
  ∑ t : Fin T, w (state (phaseHistoryPrefix s (by omega) h)) t * (h (blockRound hn t)).2

theorem measurable_blockEstimate {k n : ℕ} {State : Type*} [MeasurableSpace State]
    (s T : ℕ) (hn : s + T ≤ n) (state : BanditHistory k s → State) (hs : Measurable state)
    (w : State → Fin T → ℝ) (hw : ∀ t, Measurable (fun z => w z t)) :
    Measurable (blockEstimate s T state w hn) := by
  apply Finset.measurable_sum
  intro t _
  exact ((hw t).comp (hs.comp (measurable_phaseHistoryPrefix s (by omega)))).mul
    (measurable_snd.comp (measurable_pi_apply _))

theorem blockCenteredSum_eq_estimate_sub_mean {k n : ℕ} {State : Type*}
    (nu : StochasticBandit k) (s T : ℕ) (state : BanditHistory k s → State)
    (w : State → Fin T → ℝ) (schedule : State → Fin T → Fin k)
    (hn : s + T ≤ n) (h : BanditHistory k n) (mean : ℝ)
    (hsched : ∀ t, (h (blockRound hn t)).1 = schedule (state (phaseHistoryPrefix s (by omega) h)) t)
    (hmean : (∑ t : Fin T, w (state (phaseHistoryPrefix s (by omega) h)) t *
      banditArmMean nu (schedule (state (phaseHistoryPrefix s (by omega) h)) t)) = mean) :
    blockCenteredSum nu s T state w hn h = blockEstimate s T state w hn h - mean := by
  unfold blockCenteredSum blockEstimate
  simp_rw [hsched, mul_sub]
  rw [Finset.sum_sub_distrib, hmean]

end PhasedElimination
end

/- Complete adapted prior component: PhaseConcentrationPolicy. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace PhasedElimination

theorem blockEstimate_eq_phaseEstimate {k M n : ℕ} (p : PhasePlan k M)
    (l : ℕ) (hl : phaseStart M (l + 1) ≤ n) (h : BanditHistory k n) (j : Fin k) :
    blockEstimate (phaseStart M l) (phaseLength M l) (phaseState p l)
      (fun A => p.weights l A j) (by rwa [← phaseStart_succ]) h =
    phaseEstimate p l
      (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
      (policyPrefix hl h) j := by
  rfl

theorem phase_estimation_error_probability {k M n : ℕ}
    (hM : 0 < M) (p : PhasePlan k M) (nu : StochasticBandit k)
    (hnu : IsSubgaussianBandit 1 nu) (l : ℕ) (hl : phaseStart M (l + 1) ≤ n)
    (v : ℝ) (hv : 0 < v)
    (hvar : ∀ A j, (∑ t : Fin (phaseLength M l), (p.weights l A j t) ^ 2) ≤ v)
    (hmean : ∀ A j, A j = true →
      (∑ t : Fin (phaseLength M l), p.weights l A j t *
        banditArmMean nu (p.schedule l A t)) = banditArmMean nu j)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (banditMeasure nu (phasePolicy hM p) n).real
      {h | ∃ j, phaseState p l
          (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true ∧
        eps < |phaseEstimate p l
          (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
          (policyPrefix hl h) j - banditArmMean nu j|} ≤
      2 * k * Real.exp (-eps ^ 2 / (2 * v)) := by
  have hn : phaseStart M l + phaseLength M l ≤ n := by rwa [← phaseStart_succ]
  have htail := blockCenteredSum_family_tail nu hnu (phasePolicy hM p)
    (phaseStart M l) (phaseLength M l) hn (phaseState p l) (measurable_phaseState p l)
    (p.weights l) (fun j t => measurable_of_countable _) v hv hvar eps heps
  have hrecord := ae_recorded_schedule hM p nu l hn
  refine le_trans ?_ htail
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hrecord] with h hh
  rintro ⟨j, hj, herror⟩
  refine ⟨j, ?_⟩
  have heq := blockCenteredSum_eq_estimate_sub_mean nu
    (phaseStart M l) (phaseLength M l) (phaseState p l)
    (fun A => p.weights l A j) (p.schedule l) hn h (banditArmMean nu j)
    hh (hmean _ j hj)
  rw [heq, blockEstimate_eq_phaseEstimate p l hl]
  exact herror

end PhasedElimination
end

/- Complete adapted prior component: PhaseConcentrationConfidence. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace PhasedElimination

theorem phaseRadius_sq_mul_length (M l : ℕ) :
    (phaseRadius l) ^ 2 * (phaseLength M l : ℝ) = (M : ℝ) := by
  have hp : (((1 / 2 : ℝ) ^ l) ^ 2) * (4 : ℝ) ^ l = 1 := by
    rw [← pow_mul, Nat.mul_comm l 2, pow_mul, ← mul_pow]
    norm_num
  simp only [phaseRadius, phaseLength, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    ((1 / 2 : ℝ) ^ l) ^ 2 * ((M : ℝ) * (4 : ℝ) ^ l) =
        (M : ℝ) * (((1 / 2 : ℝ) ^ l) ^ 2 * (4 : ℝ) ^ l) := by ring
    _ = (M : ℝ) := by rw [hp, mul_one]

theorem phase_tail_le_budget {k d n M : ℕ} {delta : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hM : 0 < M) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hbase : 8 * (d : ℝ) * confidenceLog k n delta ≤ (M : ℝ)) (l : ℕ) :
    2 * k * Real.exp (-(phaseRadius l) ^ 2 / (2 * (2 * (d : ℝ) / phaseLength M l))) ≤
      delta / confidencePhases n := by
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hT : (0 : ℝ) < phaseLength M l := by exact_mod_cast phaseLength_pos hM l
  have hH : (0 : ℝ) < confidencePhases n := by exact_mod_cast confidencePhases_pos n
  have hK : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hb := confidenceLog_lower (n := n) hk hd0 hd1
  have hid := phaseRadius_sq_mul_length M l
  have hexp : -(phaseRadius l) ^ 2 / (2 * (2 * (d : ℝ) / phaseLength M l)) =
      -(M : ℝ) / (4 * d) := by
    field_simp [ne_of_gt hD, ne_of_gt hT]
    nlinarith [hid]
  have hlarge : -(M : ℝ) / (4 * d) ≤ -confidenceLog k n delta := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * d)).2
    have hdb : 0 ≤ (d : ℝ) * confidenceLog k n delta := mul_nonneg hD.le (by linarith)
    nlinarith
  rw [hexp]
  calc
    2 * k * Real.exp (-(M : ℝ) / (4 * d)) ≤
        2 * k * Real.exp (-confidenceLog k n delta) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlarge) (by positivity)
    _ = delta / confidencePhases n := by
      rw [confidenceLog, Real.exp_neg, Real.exp_log (by positivity :
        (0 : ℝ) < 2 * k * confidencePhases n / delta)]
      field_simp

def phaseAccuracyEvent {k M : ℕ} (p : PhasePlan k M) (mu : Fin k → ℝ)
    (n l : ℕ) : Set (BanditHistory k n) :=
  if hl : phaseStart M (l + 1) ≤ n then
    {h | ∀ j, phaseState p l
        (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true →
      |phaseEstimate p l
        (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
        (policyPrefix hl h) j - mu j| ≤ phaseRadius l}
  else Set.univ

def phaseConfidenceEvent {k M : ℕ} (p : PhasePlan k M) (mu : Fin k → ℝ)
    (n : ℕ) : Set (BanditHistory k n) :=
  ⋂ l : Fin (confidencePhases n), phaseAccuracyEvent p mu n l.val

theorem mem_phaseConfidenceEvent {k M n : ℕ} (p : PhasePlan k M) (mu : Fin k → ℝ)
    (h : BanditHistory k n) (hh : h ∈ phaseConfidenceEvent p mu n)
    (l : ℕ) (hl : l < confidencePhases n) (hcomplete : phaseStart M (l + 1) ≤ n)
    (j : Fin k) (hj : phaseState p l
      (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hcomplete) h) j = true) :
    |phaseEstimate p l
      (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hcomplete) h))
      (policyPrefix hcomplete h) j - mu j| ≤ phaseRadius l := by
  have hm := Set.mem_iInter.mp hh (⟨l, hl⟩ : Fin (confidencePhases n))
  simp only [phaseAccuracyEvent, dif_pos hcomplete, Set.mem_setOf_eq] at hm
  exact hm j hj

theorem measurableSet_phaseAccuracyEvent {k M : ℕ} (p : PhasePlan k M)
    (mu : Fin k → ℝ) (n l : ℕ) : MeasurableSet (phaseAccuracyEvent p mu n l) := by
  classical
  by_cases hl : phaseStart M (l + 1) ≤ n
  · simp only [phaseAccuracyEvent, dif_pos hl, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    have hA : Measurable (fun h : BanditHistory k n => phaseState p l
        (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h)) :=
      (measurable_phaseState p l).comp (measurable_policyPrefix _)
    have he : Measurable (fun h : BanditHistory k n => phaseEstimate p l
        (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
        (policyPrefix hl h) j) :=
      (measurable_pi_apply j).comp ((measurable_phaseEstimate p l).comp
        (hA.prodMk (measurable_policyPrefix hl)))
    have ha : MeasurableSet {h : BanditHistory k n | phaseState p l
        (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true} :=
      measurableSet_eq_fun ((measurable_pi_apply j).comp hA) measurable_const
    have ht := measurableSet_le (he.sub_const (mu j)).abs
      (measurable_const : Measurable (fun _ : BanditHistory k n => phaseRadius l))
    change MeasurableSet {h : BanditHistory k n |
      phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true →
        |phaseEstimate p l
          (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
          (policyPrefix hl h) j - mu j| ≤ phaseRadius l}
    have heq : {h : BanditHistory k n |
        phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true →
          |phaseEstimate p l
            (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
            (policyPrefix hl h) j - mu j| ≤ phaseRadius l} =
        {h | phaseState p l
          (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true}ᶜ ∪
        {h | |phaseEstimate p l
          (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
          (policyPrefix hl h) j - mu j| ≤ phaseRadius l} := by
      ext h
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    rw [heq]
    exact ha.compl.union ht
  · simp only [phaseAccuracyEvent, dif_neg hl]
    exact MeasurableSet.univ

theorem measurableSet_phaseConfidenceEvent {k M : ℕ} (p : PhasePlan k M)
    (mu : Fin k → ℝ) (n : ℕ) : MeasurableSet (phaseConfidenceEvent p mu n) :=
  MeasurableSet.iInter fun l => measurableSet_phaseAccuracyEvent p mu n l.val

theorem phase_accuracy_failure_probability {k d n M : ℕ} {delta : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hM : 0 < M) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hbase : 8 * (d : ℝ) * confidenceLog k n delta ≤ (M : ℝ))
    (p : PhasePlan k M) (nu : StochasticBandit k) (hnu : IsSubgaussianBandit 1 nu)
    (hvar : ∀ l A j, (∑ t : Fin (phaseLength M l), (p.weights l A j t) ^ 2) ≤
      2 * (d : ℝ) / phaseLength M l)
    (hmean : ∀ l A j, A j = true →
      (∑ t : Fin (phaseLength M l), p.weights l A j t *
        banditArmMean nu (p.schedule l A t)) = banditArmMean nu j) (l : ℕ) :
    (banditMeasure nu (phasePolicy hM p) n).real
      (phaseAccuracyEvent p (banditArmMean nu) n l)ᶜ ≤ delta / confidencePhases n := by
  classical
  by_cases hl : phaseStart M (l + 1) ≤ n
  · have heq : (phaseAccuracyEvent p (banditArmMean nu) n l)ᶜ =
        {h | ∃ j, phaseState p l
            (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true ∧
          phaseRadius l < |phaseEstimate p l
            (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
            (policyPrefix hl h) j - banditArmMean nu j|} := by
      ext h
      simp only [phaseAccuracyEvent, dif_pos hl, Set.mem_compl_iff, Set.mem_setOf_eq,
        not_forall, not_le, exists_prop]
    rw [heq]
    have hT : (0 : ℝ) < phaseLength M l := by exact_mod_cast phaseLength_pos hM l
    have hD : (0 : ℝ) < d := by exact_mod_cast hd
    exact (phase_estimation_error_probability hM p nu hnu l hl
      (2 * (d : ℝ) / phaseLength M l) (by positivity) (hvar l) (hmean l)
      (phaseRadius l) (pow_nonneg (by norm_num) _)).trans
        (phase_tail_le_budget hk hd hM hd0 hd1 hbase l)
  · simp only [phaseAccuracyEvent, dif_neg hl, Set.compl_univ, measureReal_empty]
    exact div_nonneg hd0.le (Nat.cast_nonneg _)

theorem phase_confidence_probability {k d n M : ℕ} {delta : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hM : 0 < M) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hbase : 8 * (d : ℝ) * confidenceLog k n delta ≤ (M : ℝ))
    (p : PhasePlan k M) (nu : StochasticBandit k) (hnu : IsSubgaussianBandit 1 nu)
    (hvar : ∀ l A j, (∑ t : Fin (phaseLength M l), (p.weights l A j t) ^ 2) ≤
      2 * (d : ℝ) / phaseLength M l)
    (hmean : ∀ l A j, A j = true →
      (∑ t : Fin (phaseLength M l), p.weights l A j t *
        banditArmMean nu (p.schedule l A t)) = banditArmMean nu j) :
    1 - delta ≤ (banditMeasure nu (phasePolicy hM p) n).real
      (phaseConfidenceEvent p (banditArmMean nu) n) := by
  have hH : (0 : ℝ) < confidencePhases n := by exact_mod_cast confidencePhases_pos n
  have hbad : (banditMeasure nu (phasePolicy hM p) n).real
      (phaseConfidenceEvent p (banditArmMean nu) n)ᶜ ≤ delta := by
    rw [phaseConfidenceEvent, Set.compl_iInter]
    calc
      _ ≤ ∑ l : Fin (confidencePhases n), (banditMeasure nu (phasePolicy hM p) n).real
          (phaseAccuracyEvent p (banditArmMean nu) n l.val)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _l : Fin (confidencePhases n), delta / confidencePhases n := by
        apply Finset.sum_le_sum
        intro l _
        exact phase_accuracy_failure_probability hk hd hM hd0 hd1 hbase p nu hnu hvar hmean l.val
      _ = delta := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  rw [probReal_compl_eq_one_sub (measurableSet_phaseConfidenceEvent p (banditArmMean nu) n)] at hbad
  linarith

end PhasedElimination
end

/- Complete adapted prior component: PhaseGoodTrace. -/
section
open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators

namespace PhasedElimination

def AccurateThrough {k M n : ℕ} (p : PhasePlan k M) (μ : Fin k → ℝ)
    (H : ℕ) (h : BanditHistory k n) : Prop :=
  ∀ l, l < H → ∀ hl : phaseStart M (l + 1) ≤ n, ∀ j,
    phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h) j = true →
    |phaseEstimate p l
        (phaseState p l (policyPrefix ((phaseStart_mono M (Nat.le_succ l)).trans hl) h))
        (policyPrefix hl h) j - μ j| ≤ phaseRadius l

theorem phaseState_good {k M n H : ℕ} (p : PhasePlan k M) (μ : Fin k → ℝ)
    (best : Fin k) (hmax : ∀ j, μ j ≤ μ best) (hgap : ∀ j, μ best - μ j ≤ 1)
    (h : BanditHistory k n) (hacc : AccurateThrough p μ H h)
    (l : ℕ) (hlH : l ≤ H) (hl : phaseStart M l ≤ n) :
    phaseState p l (policyPrefix hl h) best = true ∧
      ∀ j, phaseState p l (policyPrefix hl h) j = true →
        μ best - μ j ≤ 8 * phaseRadius l := by
  induction l with
  | zero =>
      constructor
      · rfl
      · intro j _
        simpa [phaseRadius] using (hgap j).trans (by norm_num : (1 : ℝ) ≤ 8)
  | succ l ih =>
      have hs : phaseStart M l ≤ n := (phaseStart_mono M (Nat.le_succ l)).trans hl
      have hp := ih (by omega) hs
      have ha := hacc l (by omega) hl
      constructor
      · simpa only [phaseState, policyPrefix_prefix] using
          updateActive_retains_best hp.1 hmax ha
      · intro j hj
        have hj' : updateActive (phaseState p l (policyPrefix hs h))
            (phaseEstimate p l (phaseState p l (policyPrefix hs h)) (policyPrefix hl h))
            (phaseRadius l) j = true := by
          simpa only [phaseState, policyPrefix_prefix] using hj
        have hg := updateActive_gap hp.1 ha hj'
        have hr : 4 * phaseRadius l = 8 * phaseRadius (l + 1) := by
          unfold phaseRadius
          rw [pow_succ]
          ring
        exact hg.trans_eq hr

theorem recorded_gap_of_accurate {k M n H : ℕ} (hk : 0 < k) (hM : 0 < M)
    (p : PhasePlan k M)
    (hsupport : ∀ l A, (activeSet A).Nonempty → ∀ t, p.schedule l A t ∈ activeSet A)
    (μ : Fin k → ℝ) (best : Fin k) (hmax : ∀ j, μ j ≤ μ best)
    (hgap : ∀ j, μ best - μ j ≤ 1) (hcover : n ≤ phaseStart M H)
    (h : BanditHistory k n) (hf : PolicyFollows hM p h) (hacc : AccurateThrough p μ H h)
    (t : Fin n) : μ best - μ (h t).1 ≤ 8 * phaseRadius (phaseIndex hM t) := by
  have hs := phaseIndex_spec hM t
  have hlH : phaseIndex hM t < H := by
    by_contra hn
    have hm := phaseStart_mono M (show H ≤ phaseIndex hM t by omega)
    omega
  have hgood := phaseState_good p μ best hmax hgap h hacc (phaseIndex hM t)
    hlH.le (hs.1.trans t.isLt.le)
  rw [hf t]
  apply hgood.2
  unfold phaseChoose
  simpa only [policyPrefix_prefix] using (mem_activeSet _ _).1
    (hsupport _ _ (phaseState_nonempty hk p _ _) _)

theorem sum_phase_envelope {M : ℕ} (hM : 0 < M) (m : ℕ) :
    (∑ t ∈ Finset.range (phaseStart M m), 8 * phaseRadius (phaseIndex hM t)) =
      ∑ l ∈ Finset.range m, (phaseLength M l : ℝ) * (8 * phaseRadius l) := by
  induction m with
  | zero => simp [phaseStart_zero]
  | succ m ih =>
      rw [phaseStart_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      calc
        (∑ t ∈ Finset.range (phaseLength M m),
            8 * phaseRadius (phaseIndex hM (phaseStart M m + t))) =
            ∑ _t ∈ Finset.range (phaseLength M m), 8 * phaseRadius m := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [phaseIndex_eq hM (Nat.le_add_right _ _) (by
            rw [phaseStart_succ]
            exact Nat.add_lt_add_left (Finset.mem_range.mp ht) _)]
        _ = (phaseLength M m : ℝ) * (8 * phaseRadius m) := by simp

theorem trace_regret_bound {k M n H : ℕ} (hk : 0 < k) (hM : 0 < M)
    (p : PhasePlan k M)
    (hsupport : ∀ l A, (activeSet A).Nonempty → ∀ t, p.schedule l A t ∈ activeSet A)
    (μ : Fin k → ℝ) (best : Fin k) (hmax : ∀ j, μ j ≤ μ best)
    (hgap : ∀ j, μ best - μ j ≤ 1) (hcover : n ≤ phaseStart M H)
    (h : BanditHistory k n) (hf : PolicyFollows hM p h) (hacc : AccurateThrough p μ H h) :
    (∑ t : Fin n, (μ best - μ (h t).1)) ≤ 32 * Real.sqrt ((n : ℝ) * M) := by
  have hR : (∑ t : Fin n, (μ best - μ (h t).1)) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _t : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun t _ ↦ hgap _)
      _ = _ := by simp
  have hphase : (∑ t : Fin n, (μ best - μ (h t).1)) ≤
      ∑ l ∈ Finset.range (phaseIndex hM n + 1),
        (phaseLength M l : ℝ) * (8 * phaseRadius l) := by
    calc
      _ ≤ ∑ t : Fin n, 8 * phaseRadius (phaseIndex hM t) := by
        exact Finset.sum_le_sum fun t _ ↦
          recorded_gap_of_accurate hk hM p hsupport μ best hmax hgap hcover h hf hacc t
      _ = ∑ t ∈ Finset.range n, 8 * phaseRadius (phaseIndex hM t) := by
        exact Fin.sum_univ_eq_sum_range (fun t ↦ 8 * phaseRadius (phaseIndex hM t)) n
      _ ≤ ∑ t ∈ Finset.range (phaseStart M (phaseIndex hM n + 1)),
          8 * phaseRadius (phaseIndex hM t) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (phaseIndex_spec hM n).2.le)
        intro t _ _
        exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
      _ = _ := sum_phase_envelope hM _
  exact phase_regret_bound hR (phaseIndex_spec hM n).1 (phaseIndex_spec hM n).2.le hphase

end PhasedElimination
end

/- Complete adapted prior component: PhaseCanonical. -/
section
open MeasureTheory BanditAlgorithm
open scoped BigOperators

namespace PhasedElimination

noncomputable def realizedRegret {k n : Nat} (nu : StochasticBandit k)
    (h : BanditHistory k n) : Real :=
  ∑ i, (armPullCount i h : Real) * banditGap nu i

theorem pullCount_eq_indicator_sum {k n : Nat} (i : Fin k) (h : BanditHistory k n) :
    (armPullCount i h : Real) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount, Finset.sum_boole]
  congr 2
  ext t
  simp

theorem measurable_pullCount {k n : Nat} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : Real)) := by
  simp_rw [pullCount_eq_indicator_sum]
  apply Finset.measurable_sum
  intro t _
  have hm : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage hm)
    measurable_const measurable_const

theorem pullCount_le_horizon {k n : Nat} (i : Fin k) (h : BanditHistory k n) :
    (armPullCount i h : Real) ≤ n := by
  rw [pullCount_eq_indicator_sum]
  calc
    (∑ t, if (h t).1 = i then (1 : Real) else 0) ≤ ∑ _ : Fin n, (1 : Real) := by
      apply Finset.sum_le_sum
      intro t _
      split <;> norm_num
    _ = n := by simp

theorem integrable_pullCount {k n : Nat} (nu : StochasticBandit k)
    (pi : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : Real))
      (banditMeasure nu pi n) := by
  apply Integrable.of_mem_Icc 0 n (measurable_pullCount i).aemeasurable
  exact Filter.Eventually.of_forall fun h ↦ ⟨Nat.cast_nonneg _, pullCount_le_horizon i h⟩

theorem realizedRegret_eq_timeSum {k n : Nat} (nu : StochasticBandit k)
    (h : BanditHistory k n) : realizedRegret nu h = ∑ t, banditGap nu (h t).1 := by
  classical
  simp_rw [realizedRegret, pullCount_eq_indicator_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp [ite_mul]

theorem measurable_realizedRegret {k n : Nat} (nu : StochasticBandit k) :
    Measurable (realizedRegret (n := n) nu) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pullCount i).mul_const _

theorem integrable_realizedRegret {k n : Nat} (nu : StochasticBandit k)
    (pi : BanditPolicy k) :
    Integrable (realizedRegret (n := n) nu) (banditMeasure nu pi n) := by
  apply integrable_finsetSum
  intro i _
  exact (integrable_pullCount nu pi i).mul_const _

theorem gap_nonnegative {k : Nat} (nu : StochasticBandit k) (i : Fin k) :
    0 ≤ banditGap nu i := by
  exact sub_nonneg.mpr (le_ciSup (Set.finite_range (banditArmMean nu)).bddAbove i)

theorem realizedRegret_nonnegative {k n : Nat} (nu : StochasticBandit k)
    (h : BanditHistory k n) : 0 ≤ realizedRegret nu h := by
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (gap_nonnegative nu i)

theorem realizedRegret_le_horizon {k n : Nat} (nu : StochasticBandit k)
    (hgap : ∀ i, banditGap nu i ≤ 1) (h : BanditHistory k n) :
    realizedRegret nu h ≤ n := by
  rw [realizedRegret_eq_timeSum]
  calc
    (∑ t, banditGap nu (h t).1) ≤ ∑ _ : Fin n, (1 : Real) :=
      Finset.sum_le_sum fun t _ ↦ hgap _
    _ = n := by simp

theorem banditRegret_eq_integral_realizedRegret {k : Nat} (nu : StochasticBandit k)
    (hInt : ∀ i, Integrable id (nu.P i)) (pi : BanditPolicy k) (n : Nat) :
    banditRegret nu pi n = ∫ h, realizedRegret nu h ∂banditMeasure nu pi n := by
  rw [bandit_regret_decomposition nu hInt pi n]
  simp only [realizedRegret]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ (integrable_pullCount nu pi i).mul_const _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const]
  ring

end PhasedElimination
end

/- Complete adapted prior component: PhaseRates. -/
section
namespace PhasedElimination

theorem confidenceLog_le_expected {k n : Nat} (hk : 2 ≤ k) (hn : 2 ≤ n) :
    confidenceLog k n (1 / (n : Real)) ≤ 3 * Real.log ((k : Real) * n) := by
  have hK : (2 : Real) ≤ k := by exact_mod_cast hk
  have hN : (2 : Real) ≤ n := by exact_mod_cast hn
  have hH : (confidencePhases n : Real) ≤ 2 * n := by
    exact_mod_cast confidencePhases_le_twice (show 1 ≤ n by omega)
  have hKsq : (4 : Real) ≤ (k : Real) ^ 2 := by nlinarith [sq_nonneg ((k : Real) - 2)]
  have hfactor : (4 : Real) ≤ (k : Real) ^ 2 * n := by
    nlinarith [mul_le_mul hKsq hN (by norm_num) (sq_nonneg (k : Real))]
  have harg : 2 * k * confidencePhases n / (1 / (n : Real)) ≤
      ((k : Real) * n) ^ 3 := by
    rw [one_div, div_inv_eq_mul]
    have hfirst := mul_le_mul_of_nonneg_left hH
      (show (0 : Real) ≤ 2 * k * n by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hfactor
      (show (0 : Real) ≤ k * (n : Real) ^ 2 by positivity)
    nlinarith
  have hp : (0 : Real) < 2 * k * confidencePhases n / (1 / (n : Real)) := by
    have := confidencePhases_pos n
    positivity
  have h := Real.log_le_log hp harg
  rw [Real.log_pow] at h
  simpa [confidenceLog] using h

theorem log_product_lower {k n : Nat} (hk : 2 ≤ k) (hn : 2 ≤ n) :
    1 ≤ Real.log ((k : Real) * n) := by
  have hK : (2 : Real) ≤ k := by exact_mod_cast hk
  have hN : (2 : Real) ≤ n := by exact_mod_cast hn
  have hprod : (4 : Real) ≤ (k : Real) * n := by
    nlinarith [mul_le_mul hK hN (by norm_num) (by positivity : (0 : Real) ≤ k)]
  have h := Real.log_le_log (by norm_num : (0 : Real) < 4) hprod
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith [Real.log_two_gt_d9]

theorem high_probability_rate {k d n : Nat} {delta : Real}
    (hk : 2 ≤ k) (hd : 0 < d) (hn : 2 ≤ n)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    32 * Real.sqrt ((n : Real) * basePhaseLength k d n delta) ≤
      1024 * Real.sqrt (n * d * Real.log (k * Real.log n / delta)) := by
  have hB := targetLog_lower hk hn hd0 hd1
  have hb := confidenceLog_le_target hk hn hd0 hd1
  have hM := (basePhaseLength_bounds (n := n) hk hd hd0 hd1).2.2
  have hM' : (basePhaseLength k d n delta : Real) ≤
      440 * d * Real.log (k * Real.log n / delta) := by
    have h := mul_le_mul_of_nonneg_left hb (show (0 : Real) ≤ 11 * d by positivity)
    nlinarith
  have hNM : (n : Real) * basePhaseLength k d n delta ≤
      1024 * (n * d * Real.log (k * Real.log n / delta)) := by
    have h := mul_le_mul_of_nonneg_left hM' (Nat.cast_nonneg n)
    have hpos : (0 : Real) ≤ n * d * Real.log (k * Real.log n / delta) := by positivity
    nlinarith
  calc
    32 * Real.sqrt ((n : Real) * basePhaseLength k d n delta) ≤
        32 * Real.sqrt (1024 * (n * d * Real.log (k * Real.log n / delta))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNM) (by norm_num)
    _ = 1024 * Real.sqrt (n * d * Real.log (k * Real.log n / delta)) := by
      rw [Real.sqrt_mul (by norm_num)]
      norm_num
      ring

theorem expected_rate {k d n : Nat} (hk : 2 ≤ k) (hd : 0 < d) (hn : 2 ≤ n) :
    32 * Real.sqrt ((n : Real) * basePhaseLength k d n (1 / (n : Real))) + 1 ≤
      1024 * Real.sqrt (n * d * Real.log ((k : Real) * n)) := by
  have hN : (2 : Real) ≤ n := by exact_mod_cast hn
  have hD : (1 : Real) ≤ d := by exact_mod_cast hd
  have hnpos : (0 : Real) < n := by linarith
  have hd0 : 0 < 1 / (n : Real) := by positivity
  have hd1 : 1 / (n : Real) < 1 := (div_lt_one hnpos).2 (by linarith)
  have hB := log_product_lower hk hn
  have hb := confidenceLog_le_expected hk hn
  have hM := (basePhaseLength_bounds (n := n) hk hd hd0 hd1).2.2
  have hM' : (basePhaseLength k d n (1 / (n : Real)) : Real) ≤
      33 * d * Real.log ((k : Real) * n) := by
    have h := mul_le_mul_of_nonneg_left hb (show (0 : Real) ≤ 11 * d by positivity)
    nlinarith
  have hNM : (n : Real) * basePhaseLength k d n (1 / (n : Real)) ≤
      256 * (n * d * Real.log ((k : Real) * n)) := by
    have h := mul_le_mul_of_nonneg_left hM' (Nat.cast_nonneg n)
    have hpos : (0 : Real) ≤ n * d * Real.log ((k : Real) * n) := by positivity
    nlinarith
  have hnd : (1 : Real) ≤ (n : Real) * d := by
    nlinarith [mul_le_mul hN hD (by norm_num) (by positivity : (0 : Real) ≤ n)]
  have hS : (1 : Real) ≤ n * d * Real.log ((k : Real) * n) := by
    nlinarith [mul_le_mul hnd hB (by norm_num)
      (show (0 : Real) ≤ n * d by positivity)]
  have hroot : 1 ≤ Real.sqrt (n * d * Real.log ((k : Real) * n)) :=
    Real.one_le_sqrt.mpr hS
  have hfinal : 32 * Real.sqrt ((n : Real) * basePhaseLength k d n (1 / (n : Real))) ≤
      512 * Real.sqrt (n * d * Real.log ((k : Real) * n)) := by
    calc
      _ ≤ 32 * Real.sqrt (256 * (n * d * Real.log ((k : Real) * n))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNM) (by norm_num)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num)]
        norm_num
        ring
  linarith

end PhasedElimination
end

/- Complete adapted prior component: PhasedEliminationConclusion. -/
section
open Matrix MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped BigOperators

namespace PhasedElimination

theorem phase_policy_regret_probability {k d n M : ℕ} {δ : ℝ}
    (hk : 2 ≤ k) (hd : 0 < d) (hM : 0 < M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hbase : 8 * (d : ℝ) * confidenceLog k n δ ≤ (M : ℝ))
    (p : PhasePlan k M)
    (hsupport : ∀ l A, (activeSet A).Nonempty → ∀ t, p.schedule l A t ∈ activeSet A)
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hgap : ∀ j, banditGap ν j ≤ 1)
    (hvar : ∀ l A j, (∑ t : Fin (phaseLength M l), (p.weights l A j t) ^ 2) ≤
      2 * (d : ℝ) / phaseLength M l)
    (hmean : ∀ l A j, A j = true →
      (∑ t : Fin (phaseLength M l), p.weights l A j t *
        banditArmMean ν (p.schedule l A t)) = banditArmMean ν j) :
    1 - δ ≤ (banditMeasure ν (phasePolicy hM p) n).real
      {h | realizedRegret ν h ≤ 32 * Real.sqrt ((n : ℝ) * M)} := by
  have hk0 : 0 < k := by omega
  letI : Nonempty (Fin k) := ⟨⟨0, hk0⟩⟩
  obtain ⟨best, hbest⟩ := exists_eq_ciSup_of_finite (f := banditArmMean ν)
  have hbest' : banditArmMean ν best = banditOptimalMean ν := hbest
  have hmax (j : Fin k) : banditArmMean ν j ≤ banditArmMean ν best := by
    rw [hbest']
    exact le_ciSup (Set.finite_range (banditArmMean ν)).bddAbove j
  have hgap' (j : Fin k) : banditArmMean ν best - banditArmMean ν j ≤ 1 := by
    rw [hbest']
    exact hgap j
  have hcover : n ≤ phaseStart M (confidencePhases n) := phaseStart_covers hM
  have hgood := phase_confidence_probability hk hd hM hδ0 hδ1 hbase p ν hν hvar hmean
  apply hgood.trans
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  filter_upwards [ae_policyFollows hM p ν n] with h hf
  intro hh
  have ha : AccurateThrough p (banditArmMean ν) (confidencePhases n) h := by
    intro l hl hcomplete j hj
    exact mem_phaseConfidenceEvent p (banditArmMean ν) h hh l hl hcomplete j hj
  have hr := trace_regret_bound hk0 hM p hsupport (banditArmMean ν) best hmax hgap'
    hcover h hf ha
  change realizedRegret ν h ≤ 32 * Real.sqrt ((n : ℝ) * M)
  simpa only [realizedRegret_eq_timeSum, banditGap, ← hbest'] using hr

theorem singleton_gap_zero (ν : StochasticBandit 1) (j : Fin 1) : banditGap ν j = 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [banditGap, banditOptimalMean]

theorem singleton_realizedRegret_zero {n : ℕ} (ν : StochasticBandit 1)
    (h : BanditHistory 1 n) : realizedRegret ν h = 0 := by
  simp [realizedRegret, singleton_gap_zero]

end PhasedElimination

open PhasedElimination

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k d n : ℕ), 0 < k → 0 < d → 2 ≤ n →
        ∀ (arms : Fin k → Fin d → ℝ) (δ : ℝ), δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ π : BanditPolicy k,
            ∀ (θstar : Fin d → ℝ) (ν : StochasticBandit k),
              IsLinearBandit arms θstar ν →
              (∀ i, banditGap ν i ≤ 1) →
              1 - δ ≤ (banditMeasure ν π n).real
                  {h | ∑ i, (armPullCount i h : ℝ) * banditGap ν i ≤
                    C * Real.sqrt (n * d * Real.log (k * Real.log n / δ))} ∧
              (δ = 1 / n →
                banditRegret ν π n ≤
                  C * Real.sqrt (n * d * Real.log (k * n))) := by
  refine ⟨1024, by norm_num, ?_⟩
  intro k d n hk hd hn arms δ hδ
  by_cases hk1 : k = 1
  · subst k
    let p : PhasePlan 1 1 := ⟨fun _ _ _ ↦ 0, fun _ _ _ _ ↦ 0⟩
    let π := phasePolicy (by decide : 0 < 1) p
    refine ⟨π, ?_⟩
    intro θstar ν hlin _
    constructor
    · have hevent : {h : BanditHistory 1 n |
          (∑ i, (armPullCount i h : ℝ) * banditGap ν i) ≤
            1024 * Real.sqrt (n * d * Real.log (1 * Real.log n / δ))} = Set.univ := by
        ext h
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        simp only [singleton_gap_zero, mul_zero, Finset.sum_const_zero]
        positivity
      simp only [Nat.cast_one]
      rw [hevent, probReal_univ]
      linarith [hδ.1]
    · intro _
      rw [banditRegret_eq_integral_realizedRegret ν hlin.2.1 π n]
      simp only [singleton_realizedRegret_zero, integral_zero]
      positivity
  · have hk2 : 2 ≤ k := by omega
    let M := basePhaseLength k d n δ
    have hMb := basePhaseLength_bounds (n := n) hk2 hd hδ.1 hδ.2
    have hMd : 2 * d ≤ M := hMb.2.1
    have hM : 0 < M := by omega
    let p := exactPhasePlan hk hd hMd arms
    let π := phasePolicy hM p
    refine ⟨π, ?_⟩
    intro θstar ν hlin hgap
    have hp : 1 - δ ≤ (banditMeasure ν π n).real
        {h | realizedRegret ν h ≤ 32 * Real.sqrt ((n : ℝ) * M)} := by
      apply phase_policy_regret_probability hk2 hd hM hδ.1 hδ.2 hMb.1 p
        (exactPhasePlan_schedule_supported hk hd hMd arms) ν hlin.2 hgap
      · exact exactPhasePlan_weight_sq_sum hk hd hMd arms
      · intro l A j hj
        exact exactPhasePlan_weighted_mean_eq hk hd hMd arms θstar (banditArmMean ν)
          hlin.1 l A j ((mem_activeSet A j).2 hj)
    constructor
    · apply hp.trans
      refine measureReal_mono ?_ (by finiteness)
      intro h hh
      exact hh.trans (high_probability_rate hk2 hd hn hδ.1 hδ.2)
    · intro hδn
      have he := integral_le_of_high_probability (measurable_realizedRegret ν)
        (integrable_realizedRegret ν π) (by positivity) (Nat.cast_nonneg n)
        (realizedRegret_le_horizon ν hgap) hp
      rw [← banditRegret_eq_integral_realizedRegret ν hlin.2.1 π n] at he
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      calc
        banditRegret ν π n ≤
            32 * Real.sqrt ((n : ℝ) * basePhaseLength k d n (1 / (n : ℝ))) + 1 := by
          simpa only [M, hδn, mul_one_div_cancel hn0] using he
        _ ≤ 1024 * Real.sqrt (n * d * Real.log ((k : ℝ) * n)) := expected_rate hk2 hd hn
end

#print axioms solution
