-- Prove2me | solution 1 for ChenWhitt93.Reflection.neumann_series_entry_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:22:49.893404+00:00
-- url     : https://prove2.me/submissions/7a6cc4bf-607c-402a-be4f-25a6b4b46f79

import Mathlib

open Filter Topology Matrix

theorem solution {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (hQ : ∀ i j, 0 ≤ Q i j) (hsum : Summable (fun k : Nat => Q ^ k)) :
    ∀ i j, 0 ≤ (∑' k : Nat, Q ^ k) i j := by
  intro i j
  have hpow : ∀ k : ℕ, ∀ a b : Fin n, 0 ≤ (Q ^ k) a b := by
    intro k
    induction k with
    | zero =>
      intro a b
      simp [pow_zero, Matrix.one_apply]
      split_ifs <;> norm_num
    | succ k ih =>
      intro a b
      rw [pow_succ, mul_apply]
      exact Finset.sum_nonneg fun r _ => mul_nonneg (ih a r) (hQ r b)
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) :=
    continuous_apply_apply i j
  let φ : Matrix (Fin n) (Fin n) ℝ →+ ℝ :=
    AddMonoidHom.mk' (fun M => M i j) (fun A B => by simp [Matrix.add_apply])
  have hhas : HasSum (fun k : ℕ => (Q ^ k) i j) ((∑' k : ℕ, Q ^ k) i j) :=
    hsum.hasSum.map φ hc
  exact hhas.tsum_eq ▸ tsum_nonneg fun k => hpow k i j
