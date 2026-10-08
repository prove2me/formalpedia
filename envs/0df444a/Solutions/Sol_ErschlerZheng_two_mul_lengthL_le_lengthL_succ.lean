-- Prove2me | solution 1 for ErschlerZheng.two_mul_lengthL_le_lengthL_succ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:32:47.094396+00:00
-- url     : https://prove2.me/submissions/5e9d33b5-5d59-4fc9-a4ed-835850c1cec2

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# A16 and A18: `(012)^∞` satisfies `Fr(5)`; `L^ω_{n+1} ⩾ 2 L^ω_n`

A18 route (the paper's idea): the row vector `r_n = (1 1 1) M_{ω_0} ⋯ M_{ω_{n-1}}` keeps each
coordinate at most the sum of the other two, and `Σ (r M_i) ⩾ 2 Σ r` for such `r`.
-/

namespace ErschlerZheng

namespace LengthsDev

/-- The row vector `(1 1 1) M_{ω_0} ⋯ M_{ω_{n-1}}`. -/
def rowVec (ω : ℕ → Fin 3) (n : ℕ) : Fin 3 → ℕ :=
  Matrix.vecMul (fun _ => 1) (List.ofFn fun i : Fin n => substMatrix (ω i)).prod

theorem rowVec_succ (ω : ℕ → Fin 3) (n : ℕ) :
    rowVec ω (n + 1) = Matrix.vecMul (rowVec ω n) (substMatrix (ω n)) := by
  unfold rowVec
  rw [List.ofFn_succ', List.prod_concat, ← Matrix.vecMul_vecMul]
  rfl

theorem lengthL_eq (ω : ℕ → Fin 3) (n : ℕ) :
    lengthL ω n = rowVec ω n 0 + rowVec ω n 1 + rowVec ω n 2 := by
  unfold lengthL
  rw [← rowVec]
  simp [dotProduct, Fin.sum_univ_three]

theorem rowVec_succ_apply (ω : ℕ → Fin 3) (n : ℕ) :
    let r := rowVec ω n
    (ω n = 0 → rowVec ω (n + 1) 0 = 2 * r 0 ∧ rowVec ω (n + 1) 1 = 2 * r 1 ∧
      rowVec ω (n + 1) 2 = r 0 + r 1 + r 2) ∧
    (ω n = 1 → rowVec ω (n + 1) 0 = 2 * r 0 ∧ rowVec ω (n + 1) 1 = r 0 + r 1 + r 2 ∧
      rowVec ω (n + 1) 2 = 2 * r 2) ∧
    (ω n = 2 → rowVec ω (n + 1) 0 = r 0 + r 1 + r 2 ∧ rowVec ω (n + 1) 1 = 2 * r 1 ∧
      rowVec ω (n + 1) 2 = 2 * r 2) := by
  intro r
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · rw [rowVec_succ, h]
    simp [substMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_three, r]
    omega

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  rcases i with ⟨k, hk⟩
  interval_cases k <;> simp

/-- Each coordinate of `r_n` is at most the sum of the other two. -/
theorem rowVec_triangle (ω : ℕ → Fin 3) (n : ℕ) :
    rowVec ω n 0 ≤ rowVec ω n 1 + rowVec ω n 2 ∧ rowVec ω n 1 ≤ rowVec ω n 0 + rowVec ω n 2 ∧
      rowVec ω n 2 ≤ rowVec ω n 0 + rowVec ω n 1 := by
  induction n with
  | zero => simp [rowVec, Matrix.vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_three]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := rowVec_succ_apply ω n
    rcases fin3_cases (ω n) with h | h | h
    · obtain ⟨a, b, c⟩ := h0 h; rw [a, b, c]; omega
    · obtain ⟨a, b, c⟩ := h1 h; rw [a, b, c]; omega
    · obtain ⟨a, b, c⟩ := h2 h; rw [a, b, c]; omega

end LengthsDev

end ErschlerZheng
end

section
open ErschlerZheng
open LengthsDev in
theorem solution (ω : ℕ → Fin 3) (n : ℕ) :
    2 * lengthL ω n ≤ lengthL ω (n + 1) := by
  rw [lengthL_eq, lengthL_eq]
  obtain ⟨t0, t1, t2⟩ := rowVec_triangle ω n
  obtain ⟨h0, h1, h2⟩ := rowVec_succ_apply ω n
  rcases fin3_cases (ω n) with h | h | h
  · obtain ⟨a, b, c⟩ := h0 h; rw [a, b, c]; omega
  · obtain ⟨a, b, c⟩ := h1 h; rw [a, b, c]; omega
  · obtain ⟨a, b, c⟩ := h2 h; rw [a, b, c]; omega
end
