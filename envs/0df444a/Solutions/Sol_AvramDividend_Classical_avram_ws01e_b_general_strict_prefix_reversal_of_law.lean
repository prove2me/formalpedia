-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_general_strict_prefix_reversal_of_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:57:45.853964+00:00
-- url     : https://prove2.me/submissions/a378819f-86f5-4bd8-b7be-52f6c958e47b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (n : ℕ) (μ : Measure (Fin n → ℝ)) (a : ℝ)
    (w : (Fin n → ℝ) → ℕ → ℝ)
    (hrev : Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ)
    (hprefix : ∀ (v : Fin n → ℝ) (k : ℕ), k ≤ n →
      Finset.sum (Finset.range k) (w (fun i => v i.rev)) =
      Finset.sum (Finset.range k) (fun j => w v (n - 1 - j))) :
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) < a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) < a} := by
  have hRm : Measurable (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  let R : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    { toFun := fun v i => v i.rev
      invFun := fun v i => v i.rev
      left_inv := fun v => by funext i; simp
      right_inv := fun v => by funext i; simp
      measurable_toFun := hRm
      measurable_invFun := hRm }
  have hprefixR (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
      Finset.sum (Finset.range k) (w (R v)) =
        Finset.sum (Finset.range k) (fun j => w v (n - 1 - j)) := by
    exact hprefix v k hk
  have hset : {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) < a} =
      R ⁻¹' {v : Fin n → ℝ | ∃ k : Fin n.succ,
        Finset.sum (Finset.range k.val) (w v) < a} := by
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
      rw [hprefixR v k' (Nat.lt_succ_iff.mp k'.isLt)]
      simp only at hk'
      rw [hk']; exact hk
    · rintro ⟨k, hk⟩
      rw [hprefixR v k (Nat.lt_succ_iff.mp k.isLt)] at hk
      have : Finset.sum (Finset.range k.val) (fun j => w v (n - 1 - j)) ∈
          Set.range (fun k : Fin n.succ =>
            Finset.sum (Finset.range k.val) (fun j => w v (n - 1 - j))) := ⟨k, rfl⟩
      rw [← hr] at this
      obtain ⟨k', hk'⟩ := this
      refine ⟨k', ?_⟩
      simp only at hk'
      rw [hk']; exact hk
  rw [hset, ← R.map_apply]
  show (Measure.map (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ) _ = _
  rw [hrev]
