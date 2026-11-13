-- Prove2me | solution 1 for CountingLLL.RandomRAM.reciprocal_stopping
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:35:22.4271+00:00
-- url     : https://prove2.me/submissions/b01f50b9-687e-435e-9de4-417bbcdcf34c

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace ResearchReciprocal

/-- At least n samples have been nonzero, so sample n+1 is requested. -/
def survive (n : ℕ) : Set (ℕ → ℝ) := {ω | ∀ i < n, ω i ≠ 0}

noncomputable def samples (ω : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, (survive n).indicator 1 ω

private theorem survive_measurable (n : ℕ) : MeasurableSet (survive n) := by
  have heq : survive n = ⋂ i : Fin n, {ω : ℕ → ℝ | ω i.val ≠ 0} := by
    ext ω
    simp only [survive, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact h i.val i.isLt
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_singleton 0).compl.preimage (measurable_pi_apply i.val)

private theorem survive_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν) (survive n) = ν {x | x ≠ 0} ^ n := by
  have h := Measure.infinitePi_pi (fun _ : ℕ => ν) (s := Finset.range n)
    (t := fun _ => ({0} : Set ℝ)ᶜ) (by intro i hi; exact (measurableSet_singleton 0).compl)
  have heq : ((Finset.range n : Finset ℕ) : Set ℕ).pi (fun _ => ({0} : Set ℝ)ᶜ) = survive n := by
    ext ω
    simp [Set.mem_pi, survive]
  rw [heq] at h
  have hset : {x : ℝ | x ≠ 0} = ({0} : Set ℝ)ᶜ := by ext x; simp
  rw [hset]
  simpa using h

/-- The expected number of requested copies, including the first zero, is a geometric sum. -/
theorem expected_samples (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∫⁻ ω, samples ω ∂(Measure.infinitePi fun _ : ℕ => ν)) =
      (1 - ν {x | x ≠ 0})⁻¹ := by
  unfold samples
  have hm : ∀ n, AEMeasurable ((survive n).indicator (1 : (ℕ → ℝ) → ℝ≥0∞))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    fun n => (measurable_const.indicator (survive_measurable n)).aemeasurable
  rw [lintegral_tsum hm]
  simp_rw [lintegral_indicator_one (survive_measurable _), survive_measure]
  exact ENNReal.tsum_geometric _

/-- If the probability of a nonzero sample is below one, a zero is reached almost surely. -/
theorem hits_zero_ae (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hτ : ν {x | x ≠ 0} < 1) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∃ n, ω n = 0 := by
  rw [ae_iff]
  have hzero : (Measure.infinitePi fun _ : ℕ => ν) {ω | ∀ n, ω n ≠ 0} = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hτ)
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ (Measure.infinitePi fun _ : ℕ => ν) (survive n) := measure_mono (by intro ω h i hi; exact h i)
      _ = ν {x | x ≠ 0} ^ n := survive_measure ν n
  simpa using hzero

/-- On a tape whose first zero is at index k, the count is k+1. -/
theorem samples_first_zero (ω : ℕ → ℝ) (k : ℕ) (hzero : ω k = 0)
    (hprev : ∀ j < k, ω j ≠ 0) : samples ω = (k + 1 : ℕ) := by
  classical
  unfold samples
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · have hsum : (∑ n ∈ Finset.range (k + 1), (survive n).indicator 1 ω) =
        ∑ _n ∈ Finset.range (k + 1), (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ≤ k := by simpa using hn
      have hw : ω ∈ survive n := fun j hj => hprev j (by omega)
      simp [hw]
    rw [hsum]
    simp
  · intro n hn
    have hk : k < n := by simpa using hn
    have hw : ω ∉ survive n := by
      intro h
      exact h k hk hzero
    simp [hw]

end ResearchReciprocal

open ResearchReciprocal

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∀ n : ℕ, (Measure.infinitePi fun _ : ℕ => ν) {ω | ∀ i < n, ω i ≠ 0} =
      ν {x | x ≠ 0} ^ n) ∧
    (ν {x | x ≠ 0} < 1 → ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∃ n, ω n = 0) ∧
    (∫⁻ ω, ∑' n : ℕ, ({ω' : ℕ → ℝ | ∀ i < n, ω' i ≠ 0}).indicator 1 ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) = (1 - ν {x | x ≠ 0})⁻¹ ∧
    (∀ (ω : ℕ → ℝ) (k : ℕ), ω k = 0 → (∀ j < k, ω j ≠ 0) →
      (∑' n : ℕ, ({ω' : ℕ → ℝ | ∀ i < n, ω' i ≠ 0}).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω) = (k + 1 : ℕ)) := by
  exact ⟨fun n => ResearchReciprocal.survive_measure ν n,
    ResearchReciprocal.hits_zero_ae ν, ResearchReciprocal.expected_samples ν,
    fun ω k hz hp => by simpa [samples, survive, Nat.cast_add] using
      ResearchReciprocal.samples_first_zero ω k hz hp⟩
