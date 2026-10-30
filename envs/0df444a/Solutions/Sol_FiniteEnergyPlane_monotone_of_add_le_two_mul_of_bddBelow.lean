-- Prove2me | solution 1 for FiniteEnergyPlane.monotone_of_add_le_two_mul_of_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T20:49:42.397636+00:00
-- url     : https://prove2.me/submissions/73de4edb-168f-4d24-9b48-f0b024d07c6c

import Mathlib



namespace FiniteEnergyPlane

/-- A real sequence on `ℕ` that is bounded below and satisfies `a k + a (k + 2) ≤ 2 a (k + 1)` for
all `k` is monotone. -/
theorem monotone_of_add_le_two_mul_of_bddBelow_aux (a : ℕ → ℝ) (m : ℝ) (hm : ∀ k, m ≤ a k)
    (hc : ∀ k, a k + a (k + 2) ≤ 2 * a (k + 1)) : Monotone a := by
  refine monotone_nat_of_le_succ (fun j => ?_)
  by_contra hlt
  push_neg at hlt
  set d := a j - a (j + 1) with hd
  have hd0 : 0 < d := by linarith
  have hD : ∀ i : ℕ, a (j + i + 1) - a (j + i) ≤ -d := by
    intro i
    induction i with
    | zero => simp [hd]
    | succ i ih =>
      have h := hc (j + i)
      rw [show j + (i + 1) + 1 = j + i + 2 by omega, show j + (i + 1) = j + i + 1 by omega]
      linarith
  have hA : ∀ i : ℕ, a (j + i) ≤ a j - i * d := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h := hD i
      rw [show j + (i + 1) = j + i + 1 by omega]
      push_cast
      linarith
  obtain ⟨i, hi⟩ := exists_nat_gt ((a j - m) / d)
  rw [div_lt_iff₀ hd0] at hi
  have := hA i
  have := hm (j + i)
  linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (a : ℕ → ℝ) (m : ℝ) (hm : ∀ k, m ≤ a k)
    (hc : ∀ k, a k + a (k + 2) ≤ 2 * a (k + 1)) : Monotone a :=
  monotone_of_add_le_two_mul_of_bddBelow_aux a m hm hc
