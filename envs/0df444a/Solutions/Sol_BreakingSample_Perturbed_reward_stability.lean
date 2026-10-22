-- Prove2me | solution 1 for BreakingSample.Perturbed.reward_stability
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:36:10.694908+00:00
-- url     : https://prove2.me/submissions/09a72539-017a-4c40-bfc2-1bf4a8d32e80

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

set_option autoImplicit false
open BreakingSample.Perturbed FoundationsML.ReinforcementLearning

lemma CC_it {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (π : S → A) (s s' : S) :
    InducedTransition (detPolicy π) P s s' = P s (π s) s' := by
  simp [InducedTransition, detPolicy]

lemma CC_ir {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (r : S → A → ℝ) (π : S → A) (s : S) :
    InducedReward (detPolicy π) r s = r s (π s) := by
  simp [InducedReward, detPolicy]

lemma CC_occ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A) (s0 : S) :
    ∀ t, (∀ s, 0 ≤ OccupationDist (detPolicy π) P s0 t s) ∧
      ∑ s, OccupationDist (detPolicy π) P s0 t s = 1 := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · simp only [OccupationDist]; split_ifs <;> norm_num
    · simp [OccupationDist]
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun s' => ?_, ?_⟩
    · simp only [OccupationDist, CC_it]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (h1 s) ((hP s (π s)).1 s')
    · simp only [OccupationDist, CC_it]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (hP _ _).2, mul_one]
      exact h2

lemma CC_term_bound {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A) (s0 : S) (R : S → ℝ) (t : ℕ) :
    |∑ s', OccupationDist (detPolicy π) P s0 t s' * R s'| ≤ ∑ s', |R s'| := by
  obtain ⟨h1, h2⟩ := CC_occ P hP π s0 t
  calc |∑ s', OccupationDist (detPolicy π) P s0 t s' * R s'|
      ≤ ∑ s', |OccupationDist (detPolicy π) P s0 t s' * R s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', |R s'| := by
        apply Finset.sum_le_sum
        intro s' _
        rw [abs_mul, abs_of_nonneg (h1 s')]
        have : OccupationDist (detPolicy π) P s0 t s' ≤ 1 := by
          rw [← h2]
          exact Finset.single_le_sum (fun i _ => h1 i) (Finset.mem_univ s')
        exact mul_le_of_le_one_left (abs_nonneg _) this

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r r' : S → A → ℝ) (γ ξ : ℝ)
    (hP : IsTransitionKernel P) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hξ : 0 ≤ ξ) (hr : ∀ s a, |r s a - r' s a| ≤ ξ) :
    ∀ (π : S → A) (s : S),
      |value P r γ π s - value P r' γ π s| ≤ ξ / (1 - γ) := by
  intro π s
  unfold value PolicyValue
  have hsum : ∀ q : S → A → ℝ, Summable (fun t : ℕ => γ ^ t *
      ∑ s', OccupationDist (detPolicy π) P s t s' * InducedReward (detPolicy π) q s') := by
    intro q
    have hg : Summable (fun t : ℕ => γ ^ t * ∑ s', |InducedReward (detPolicy π) q s'|) :=
      (summable_geometric_of_lt_one hγ₀ hγ₁).mul_right _
    refine Summable.of_norm_bounded hg (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ₀ t)]
    exact mul_le_mul_of_nonneg_left (CC_term_bound P hP π s _ t) (pow_nonneg hγ₀ t)
  rw [← Summable.tsum_sub (hsum r) (hsum r')]
  have hgs : HasSum (fun t : ℕ => γ ^ t * ξ) (ξ / (1 - γ)) := by
    have := (hasSum_geometric_of_lt_one hγ₀ hγ₁).mul_right ξ
    rw [div_eq_inv_mul]
    exact this
  have := tsum_of_norm_bounded hgs (f := fun t : ℕ => γ ^ t *
      ∑ s', OccupationDist (detPolicy π) P s t s' * InducedReward (detPolicy π) r s' -
      γ ^ t * ∑ s', OccupationDist (detPolicy π) P s t s' * InducedReward (detPolicy π) r' s') (fun t => ?_)
  · simpa using this
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hγ₀ t), ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ₀ t)
    obtain ⟨h1, h2⟩ := CC_occ P hP π s t
    have : ∀ s', OccupationDist (detPolicy π) P s t s' * InducedReward (detPolicy π) r s' -
        OccupationDist (detPolicy π) P s t s' * InducedReward (detPolicy π) r' s' =
        OccupationDist (detPolicy π) P s t s' * (r s' (π s') - r' s' (π s')) := by
      intro s'; rw [← mul_sub, CC_ir, CC_ir]
    simp_rw [this]
    calc |∑ s', OccupationDist (detPolicy π) P s t s' * (r s' (π s') - r' s' (π s'))|
        ≤ ∑ s', |OccupationDist (detPolicy π) P s t s' * (r s' (π s') - r' s' (π s'))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', OccupationDist (detPolicy π) P s t s' * ξ := by
          apply Finset.sum_le_sum
          intro s' _
          rw [abs_mul, abs_of_nonneg (h1 s')]
          exact mul_le_mul_of_nonneg_left (hr s' (π s')) (h1 s')
      _ = ξ := by rw [← Finset.sum_mul, h2, one_mul]
