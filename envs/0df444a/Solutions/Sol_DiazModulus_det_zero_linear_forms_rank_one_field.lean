-- Prove2me | solution 1 for DiazModulus.det_zero_linear_forms_rank_one_field
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T04:58:28.162177+00:00
-- url     : https://prove2.me/submissions/2f353c65-48fb-4b3e-96d4-bdb4bdf7ef13

import Mathlib

namespace P14Field

/-- If the symmetrised tensor `u ⊗ v + v ⊗ u` of two vectors over a field of characteristic zero
vanishes, then one of the two vectors vanishes: a product of two nonzero linear forms is a nonzero
quadratic form. -/
theorem sym_eq_zero {F : Type*} [Field F] [CharZero F] {n : ℕ} (u v : Fin n → F)
    (h : ∀ k l, u k * v l + u l * v k = 0) :
    (∀ k, u k = 0) ∨ (∀ k, v k = 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hc
  have hvi : v i = 0 := by
    have hii : (2 : F) * (u i * v i) = 0 := by linear_combination h i i
    have hii' : u i * v i = 0 := (mul_eq_zero.1 hii).resolve_left two_ne_zero
    exact (mul_eq_zero.1 hii').resolve_left hi
  have huj : u j = 0 := by
    have hjj : (2 : F) * (u j * v j) = 0 := by linear_combination h j j
    have hjj' : u j * v j = 0 := (mul_eq_zero.1 hjj).resolve_left two_ne_zero
    exact (mul_eq_zero.1 hjj').resolve_right hj
  have hij := h i j
  rw [huj, hvi, mul_zero, add_zero] at hij
  exact mul_ne_zero hi hj hij

end P14Field

open P14Field in
/-- Write `a, b, c, d` for the coefficient vectors of `L₀₀, L₀₁, L₁₀, L₁₁`.
If `a = 0` then `sym(b ⊗ c) = 0`, so `b = 0` (a zero row) or `c = 0` (a zero column).
Otherwise pick `k` with `α = a k ≠ 0`. The diagonal and the `k`-th row of the hypothesis give
`α² d = α b_k c + α c_k b - b_k c_k a`, and then `sym((α b - b_k a) ⊗ (α c - c_k a)) = 0`.
So either `α b = b_k a`, and then `α d = b_k c` (column 1 is proportional to column 0),
or `α c = c_k a`, and then `α d = c_k b` (row 1 is proportional to row 0).
The field `F` only needs characteristic zero, to divide by `2`. -/
theorem solution {F : Type*} [Field F] [CharZero F] (n : ℕ)
    (A : Fin 2 → Fin 2 → Fin n → F)
    (hdet : ∀ k l : Fin n,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k) :
    (∃ p q : F, ¬(p = 0 ∧ q = 0) ∧ ∀ j k, p * A 0 j k + q * A 1 j k = 0) ∨
      (∃ p q : F, ¬(p = 0 ∧ q = 0) ∧ ∀ i k, p * A i 0 k + q * A i 1 k = 0) := by
  by_cases ha : ∀ k, A 0 0 k = 0
  · -- `L₀₀ = 0`, so `L₀₁ · L₁₀ = 0`
    have h0 : ∀ k l, A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k = 0 := by
      intro k l
      linear_combination (-1 : F) * hdet k l + A 1 1 l * ha k + A 1 1 k * ha l
    rcases sym_eq_zero _ _ h0 with hb | hc
    · -- row 0 vanishes
      left
      refine ⟨1, 0, by simp, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · intro k
        simp [ha k]
      · intro k
        simp [hb k]
    · -- column 0 vanishes
      right
      refine ⟨1, 0, by simp, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · intro k
        simp [ha k]
      · intro k
        simp [hc k]
  · push Not at ha
    obtain ⟨k, hk⟩ := ha
    -- `α² d = α b_k c + α c_k b - b_k c_k a`, with `α = a_k`
    have hd : ∀ l, A 0 0 k ^ 2 * A 1 1 l = A 0 0 k * A 0 1 k * A 1 0 l
        + A 0 0 k * A 1 0 k * A 0 1 l - A 0 1 k * A 1 0 k * A 0 0 l := by
      intro l
      linear_combination A 0 0 k * hdet k l - (A 0 0 l / 2) * hdet k k
    -- `sym((α b - b_k a) ⊗ (α c - c_k a)) = 0`
    have huv : ∀ l m, (A 0 0 k * A 0 1 l - A 0 1 k * A 0 0 l) * (A 0 0 k * A 1 0 m - A 1 0 k * A 0 0 m)
        + (A 0 0 k * A 0 1 m - A 0 1 k * A 0 0 m) * (A 0 0 k * A 1 0 l - A 1 0 k * A 0 0 l) = 0 := by
      intro l m
      linear_combination (-(A 0 0 k) ^ 2) * hdet l m + A 0 0 l * hd m + A 0 0 m * hd l
    rcases sym_eq_zero (fun l => A 0 0 k * A 0 1 l - A 0 1 k * A 0 0 l)
        (fun l => A 0 0 k * A 1 0 l - A 1 0 k * A 0 0 l) huv with hu | hv
    · -- `α b = b_k a`: column 1 is proportional to column 0
      have hu' : ∀ l, A 0 0 k * A 0 1 l - A 0 1 k * A 0 0 l = 0 := hu
      right
      refine ⟨A 0 1 k, -A 0 0 k, fun h => hk (neg_eq_zero.1 h.2), Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · intro l
        linear_combination (-1 : F) * hu' l
      · intro l
        apply mul_left_cancel₀ hk
        linear_combination (-(A 1 0 k)) * hu' l - hd l
    · -- `α c = c_k a`: row 1 is proportional to row 0
      have hv' : ∀ l, A 0 0 k * A 1 0 l - A 1 0 k * A 0 0 l = 0 := hv
      left
      refine ⟨A 1 0 k, -A 0 0 k, fun h => hk (neg_eq_zero.1 h.2), Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
      · intro l
        linear_combination (-1 : F) * hv' l
      · intro l
        apply mul_left_cancel₀ hk
        linear_combination (-(A 0 1 k)) * hv' l - hd l

#print axioms solution
