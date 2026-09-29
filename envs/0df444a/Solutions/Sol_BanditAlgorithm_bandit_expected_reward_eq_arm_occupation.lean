-- Prove2me | solution 1 for BanditAlgorithm.bandit_expected_reward_eq_arm_occupation
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-18T17:04:29.044661+00:00
-- url     : https://prove2.me/submissions/cdf45b26-c875-4abc-836c-d40d8b44fafc

import Definitions.Def_banditRegret

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

theorem solution {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.banditMeasure ν π n) =
      ∑ i, BanditAlgorithm.banditArmMean ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n) := by
  exact BanditAlgorithm.expected_reward_eq_arm_occupation_test ν hInt π n
