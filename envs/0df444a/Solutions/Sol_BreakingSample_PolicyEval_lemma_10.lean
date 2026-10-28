-- Prove2me | solution 1 for BreakingSample.PolicyEval.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:08:13.90999+00:00
-- url     : https://prove2.me/submissions/97fb4dfa-b06e-4d34-a555-b569cacbf77b

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

open FoundationsML.ReinforcementLearning Matrix

open BreakingSample.Perturbed in
theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A) (γ : ℝ) (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) :
    HasSum (fun i : ℕ => (γ • BreakingSample.Perturbed.policyMatrix P π) ^ i) (BreakingSample.Perturbed.resolvent P γ π) ∧
    (∀ i j, 0 ≤ BreakingSample.Perturbed.resolvent P γ π i j) ∧
    (∀ i, ∑ j, |BreakingSample.Perturbed.resolvent P γ π i j| ≤ 1 / (1 - γ)) ∧
    (∀ s, (1 - γ) * (BreakingSample.Perturbed.resolvent P γ π *ᵥ fun _ => (1 : ℝ)) s = 1) ∧
    (∀ r₁ r₂ : S → ℝ, (∀ s, 0 ≤ r₁ s) → (∀ s, r₁ s ≤ r₂ s) →
      ∀ s, 0 ≤ (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₁) s ∧
        (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₁) s ≤ (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₂) s) := by
  set M : Matrix S S ℝ := γ • policyMatrix P π with hM
  have hMnn : ∀ i j, 0 ≤ M i j := fun i j => by
    simp only [hM, Matrix.smul_apply, smul_eq_mul, policyMatrix]
    exact mul_nonneg hγ₀.le ((hP i (π i)).1 j)
  have hMrow : ∀ i, ∑ j, M i j = γ := fun i => by
    simp only [hM, Matrix.smul_apply, smul_eq_mul, policyMatrix, ← Finset.mul_sum,
      (hP i (π i)).2, mul_one]
  -- powers
  have hpow : ∀ n : ℕ, (∀ i j, 0 ≤ (M ^ n) i j) ∧ ∀ i, ∑ j, (M ^ n) i j = γ ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i j => ?_, fun i => ?_⟩
      · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
      · simp [Matrix.one_apply]
    | succ n ih =>
      refine ⟨fun i j => ?_, fun i => ?_⟩
      · rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih.1 i k) (hMnn k j))
      · rw [pow_succ]
        simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hMrow]
        rw [← Finset.sum_mul, ih.2 i, pow_succ]
  have hle : ∀ n i j, (M ^ n) i j ≤ γ ^ n := by
    intro n i j
    rw [← (hpow n).2 i]
    exact Finset.single_le_sum (f := fun j => (M ^ n) i j) (fun k _ => (hpow n).1 i k)
      (Finset.mem_univ j)
  have hgeo : Summable (fun n : ℕ => γ ^ n) := summable_geometric_of_lt_one hγ₀.le hγ₁
  have hent : ∀ i j, Summable (fun n : ℕ => (M ^ n) i j) := fun i j =>
    Summable.of_nonneg_of_le (fun n => (hpow n).1 i j) (fun n => hle n i j) hgeo
  have hsum : Summable (fun n : ℕ => M ^ n) := by
    apply Pi.summable.2
    intro i
    apply Pi.summable.2
    intro j
    exact hent i j
  set Sm := ∑' n : ℕ, M ^ n with hSm
  have hSM : Sm * (1 - M) = 1 := by
    have h1 : Sm * M = ∑' n : ℕ, M ^ (n + 1) := by
      rw [hSm, ← hsum.tsum_mul_right]
      congr 1
    have h2 : Sm = M ^ 0 + ∑' n : ℕ, M ^ (n + 1) := hsum.tsum_eq_zero_add
    rw [mul_sub, mul_one, h1]
    rw [pow_zero] at h2
    rw [h2]
    abel
  have hres : BreakingSample.Perturbed.resolvent P γ π = Sm := by
    unfold BreakingSample.Perturbed.resolvent
    exact Matrix.inv_eq_left_inv hSM
  have hRM : BreakingSample.Perturbed.resolvent P γ π * (1 - M) = 1 := by rw [hres]; exact hSM
  have hentry : ∀ i j, BreakingSample.Perturbed.resolvent P γ π i j = ∑' n : ℕ, (M ^ n) i j := by
    intro i j
    rw [hres]
    exact (Pi.hasSum.1 (Pi.hasSum.1 hsum.hasSum i) j).tsum_eq.symm
  have hnn : ∀ i j, 0 ≤ BreakingSample.Perturbed.resolvent P γ π i j := fun i j => by
    rw [hentry]; exact tsum_nonneg (fun n => (hpow n).1 i j)
  have hv : (1 - M) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 - γ := by
    funext i
    show ∑ j, (1 - M) i j * 1 = 1 - γ
    simp only [mul_one, Matrix.sub_apply, Finset.sum_sub_distrib, hMrow, Matrix.one_apply,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hone : ∀ s, (1 - γ) * (BreakingSample.Perturbed.resolvent P γ π *ᵥ fun _ => (1 : ℝ)) s = 1 := by
    intro s
    have h3 : BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun _ => 1 - γ) = fun _ => (1 : ℝ) := by
      rw [← hv, Matrix.mulVec_mulVec, hRM, Matrix.one_mulVec]
    have h4 : (fun _ : S => (1 : ℝ) - γ) = (1 - γ) • (fun _ : S => (1 : ℝ)) := by
      funext x; simp
    rw [h4, Matrix.mulVec_smul] at h3
    have := congrFun h3 s
    simpa using this
  refine ⟨hres ▸ hsum.hasSum, hnn, ?_, hone, ?_⟩
  · intro i
    have h := hone i
    have hγ' : 0 < 1 - γ := by linarith
    simp only [abs_of_nonneg (hnn i _)]
    have : ∑ j, BreakingSample.Perturbed.resolvent P γ π i j =
        (BreakingSample.Perturbed.resolvent P γ π *ᵥ fun _ => (1 : ℝ)) i := by
      simp [Matrix.mulVec, dotProduct]
    rw [this, le_div_iff₀ hγ', mul_comm]
    exact h.le
  · intro r₁ r₂ h0 h12 s
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnn s j) (h0 j))
    · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h12 j) (hnn s j))
