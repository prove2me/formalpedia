-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:06:35.242575+00:00
-- url     : https://prove2.me/submissions/9e8f8000-be04-4ef8-b535-163dedb268ba

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
theorem solution
    (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ) :
    let w : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) ≤ a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) ≤ a} := by
  intro w
  have hRm : Measurable (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  let R : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    { toFun := fun v i => v i.rev
      invFun := fun v i => v i.rev
      left_inv := fun v => by funext i; simp
      right_inv := fun v => by funext i; simp
      measurable_toFun := hRm
      measurable_invFun := hRm }
  have key : ∀ v : Fin n → ℝ, ∀ k : ℕ, k ≤ n →
      Finset.sum (Finset.range k) (w (R v)) =
        Finset.sum (Finset.range k) (fun j => w v (n - 1 - j)) := by
    intro v k hk
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk
    have h2 : n - 1 - j < n := by omega
    simp only [w, dif_pos hj', dif_pos h2]
    show v (Fin.rev ⟨j, hj'⟩) = _
    congr 1
    ext; simp [Fin.rev]; omega
  have hset : {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) ≤ a} =
      R ⁻¹' {v : Fin n → ℝ | ∃ k : Fin n.succ,
        Finset.sum (Finset.range k.val) (w v) ≤ a} := by
    ext v
    have hr := AvramDividend.Classical.finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b (w v) n
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk⟩
      have : (Finset.sum (Finset.range n) (w v) - Finset.sum (Finset.range k.val) (w v)) ∈
          Set.range (fun k : Fin n.succ => Finset.sum (Finset.range n) (w v) -
            Finset.sum (Finset.range k.val) (w v)) := ⟨k, rfl⟩
      rw [hr] at this
      obtain ⟨k', hk'⟩ := this
      refine ⟨k', ?_⟩
      rw [key v k' (Nat.lt_succ_iff.mp k'.isLt)]
      simp only at hk'
      rw [hk']; exact hk
    · rintro ⟨k, hk⟩
      rw [key v k (Nat.lt_succ_iff.mp k.isLt)] at hk
      have : Finset.sum (Finset.range k.val) (fun j => w v (n - 1 - j)) ∈
          Set.range (fun k : Fin n.succ =>
            Finset.sum (Finset.range k.val) (fun j => w v (n - 1 - j))) := ⟨k, rfl⟩
      rw [← hr] at this
      obtain ⟨k', hk'⟩ := this
      refine ⟨k', ?_⟩
      simp only at hk'
      rw [hk']; exact hk
  rw [hset, ← R.map_apply]
  show (MeasureTheory.Measure.map (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ) _ = _
  rw [hrev]
