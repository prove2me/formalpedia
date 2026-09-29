-- Prove2me | solution 1 for BanditAlgorithm.bandit_bounded_stopping_klDiv_le_expected_information
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T20:34:11.943616+00:00
-- url     : https://prove2.me/submissions/ce5eb1ce-d6e8-419a-90d3-c22e2b7b465e

import Theorems.Thm_BanditAlgorithm_bandit_stopped_klDiv_one_step

open MeasureTheory ProbabilityTheory InformationTheory ENNReal
open scoped ENNReal

namespace BanditAlgorithm

private noncomputable def stoppedArmCount {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ∑' t : ℕ,
    if (t : ℕ∞) < min (τ ω) n ∧ (ω t).1 = i then 1 else 0

private lemma stoppedArmCount_eq_sum_range {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    stoppedArmCount τ i n ω =
      ∑ t ∈ Finset.range n,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then 1 else 0 := by
  rw [stoppedArmCount, tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    simp only [Finset.mem_range, not_lt] at ht
    simp [not_lt_of_ge ht]

private lemma stoppedArmCount_succ {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (i : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    stoppedArmCount τ i (n + 1) ω =
      stoppedArmCount τ i n ω +
        if (n : ℕ∞) < τ ω ∧ (ω n).1 = i then 1 else 0 := by
  rw [stoppedArmCount_eq_sum_range, stoppedArmCount_eq_sum_range,
    Finset.sum_range_succ]

private lemma measurable_stoppedStepEvent {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    MeasurableSet {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
  have ha : Measurable (fun ω : ℕ → Fin k × ℝ ↦ (ω n).1) :=
    measurable_fst.comp (measurable_pi_apply n)
  exact (hτ.measurableSpace_le _ (hτ.measurableSet_gt' n)).inter
    (ha (measurableSet_singleton i))

private lemma measurable_stoppedArmCount {k : ℕ}
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    Measurable (stoppedArmCount τ i n) := by
  rw [show stoppedArmCount τ i n =
      fun ω ↦ ∑ t ∈ Finset.range n,
        if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then 1 else 0 by
    funext ω
    exact stoppedArmCount_eq_sum_range τ i n ω]
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurable_stoppedStepEvent τ hτ i t)
    measurable_const measurable_const

private lemma lintegral_stoppedArmCount_succ {k : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (i : Fin k) (n : ℕ) :
    (∫⁻ ω, stoppedArmCount τ i (n + 1) ω ∂banditTrajMeasure ν π) =
      (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) +
        (banditTrajMeasure ν π) {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} := by
  rw [lintegral_congr (fun ω ↦ stoppedArmCount_succ τ i n ω),
    lintegral_add_left (measurable_stoppedArmCount τ hτ i n)]
  have hE := measurable_stoppedStepEvent τ hτ i n
  rw [show (fun ω : ℕ → Fin k × ℝ ↦
      if (n : ℕ∞) < τ ω ∧ (ω n).1 = i then (1 : ℝ≥0∞) else 0) =
      {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i}.indicator (fun _ ↦ 1) by
        funext ω
        by_cases h : (n : ℕ∞) < τ ω ∧ (ω n).1 = i <;> simp [h]]
  rw [lintegral_indicator hE]
  simp

private lemma banditFiltration_zero {k : ℕ} :
    banditFiltration k 0 = ⊥ := by
  unfold banditFiltration
  change MeasurableSpace.comap (banditTrajPrefix k 0) inferInstance = ⊥
  have hconst :
      banditTrajPrefix k 0 =
        fun _ω : ℕ → Fin k × ℝ ↦ (fun t : Fin 0 ↦ t.elim0) := by
    funext ω t
    exact t.elim0
  rw [hconst, MeasurableSpace.comap_const]

private lemma bandit_stopped_klDiv_zero {k : ℕ}
    (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const 0).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const 0).measurableSpace_le) = 0 := by
  have hm : (hτ.min_const 0).measurableSpace = ⊥ := by
    calc
      (hτ.min_const 0).measurableSpace =
          hτ.measurableSpace ⊓ banditFiltration k 0 :=
        hτ.measurableSpace_min_const
      _ = ⊥ := by rw [banditFiltration_zero, inf_bot_eq]
  have hmeasure :
      @Measure.trim (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
          inferInstance (banditTrajMeasure ν π)
          (hτ.min_const 0).measurableSpace_le =
        @Measure.trim (ℕ → Fin k × ℝ) (hτ.min_const 0).measurableSpace
          inferInstance (banditTrajMeasure ν' π)
          (hτ.min_const 0).measurableSpace_le := by
    letI : MeasurableSpace (ℕ → Fin k × ℝ) :=
      (hτ.min_const 0).measurableSpace
    apply Measure.ext
    intro s hs
    have hsbot : @MeasurableSet (ℕ → Fin k × ℝ) ⊥ s := by
      rw [← hm]
      exact hs
    rcases MeasurableSpace.measurableSet_bot_iff.mp hsbot with rfl | rfl
    · simp
    · rw [trim_measurableSet_eq (hτ.min_const 0).measurableSpace_le
          (@MeasurableSet.univ _ (hτ.min_const 0).measurableSpace),
        trim_measurableSet_eq (hτ.min_const 0).measurableSpace_le
          (@MeasurableSet.univ _ (hτ.min_const 0).measurableSpace)]
      simp
  rw [hmeasure, klDiv_self]

theorem _root_.solution
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < min (τ ω) n ∧ (ω t).1 = i
            then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  change
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) *
        klDiv (ν.P i) (ν'.P i)
  induction n with
  | zero =>
      rw [bandit_stopped_klDiv_zero ν ν' π τ hτ]
      exact bot_le
  | succ n ih =>
      refine (bandit_stopped_klDiv_one_step ν ν' π τ hτ n).trans ?_
      calc
        @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
              ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
              ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) +
            ∑ i, (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
              klDiv (ν.P i) (ν'.P i) ≤
            (∑ i, (∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) *
              klDiv (ν.P i) (ν'.P i)) +
            ∑ i, (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i} *
              klDiv (ν.P i) (ν'.P i) :=
          add_le_add_left ih _
        _ = ∑ i,
            ((∫⁻ ω, stoppedArmCount τ i n ω ∂banditTrajMeasure ν π) +
              (banditTrajMeasure ν π)
                {ω | (n : ℕ∞) < τ ω ∧ (ω n).1 = i}) *
              klDiv (ν.P i) (ν'.P i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [add_mul]
        _ = ∑ i, (∫⁻ ω, stoppedArmCount τ i (n + 1) ω
              ∂banditTrajMeasure ν π) *
              klDiv (ν.P i) (ν'.P i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [lintegral_stoppedArmCount_succ ν π τ hτ]

end BanditAlgorithm
