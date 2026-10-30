-- Prove2me | solution 1 for DiazModulus.nat_telescope_iter
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:21:37.079704+00:00
-- url     : https://prove2.me/submissions/31ec5a1a-e43a-4826-8420-50e947f57e42

import Mathlib
import Theorems.Thm_DiazModulus_nat_telescope_step

open Complex ComplexConjugate

/-! # The iterated telescope: `2^{j(j−1)/2} u^j f_j(u) ≤ f_0(2^j u)`

Induction on `j`, for every `u` at once. For `j = 0` both sides are `f_0(u)`. For `j + 1`, the
step `nat_telescope_step` with `f := f_j`, `g := f_{j+1}` (monotone, and
`f_{j+1}(v+1) + f_j(v) ≤ f_j(v+1)`) gives `u · f_{j+1}(u) ≤ f_j(2u)`; the induction hypothesis
at `2u` gives `2^{j(j−1)/2} (2u)^j f_j(2u) ≤ f_0(2^j · 2u)`. Multiplying the step by
`2^{j(j−1)/2} 2^j u^j` and using `j(j−1)/2 + j = (j+1)j/2` and `2^j · 2u = 2^{j+1} u` closes it. -/

namespace C11_telescopeIter

/-- `(j + 1) j / 2 = j (j − 1) / 2 + j`. -/
theorem tri_succ (j : ℕ) : (j + 1) * (j + 1 - 1) / 2 = j * (j - 1) / 2 + j := by
  have e : (j + 1) * (j + 1 - 1) = j * (j - 1) + j * 2 := by
    cases j with
    | zero => rfl
    | succ n => simp only [Nat.add_sub_cancel]; ring
  rw [e, Nat.add_mul_div_right _ _ (by norm_num)]

end C11_telescopeIter

open C11_telescopeIter in
theorem solution (f : ℕ → ℕ → ℕ) (j : ℕ) (hmono : ∀ k < j, Monotone (f (k + 1)))
    (h : ∀ k < j, ∀ v, f (k + 1) (v + 1) + f k v ≤ f k (v + 1)) (u : ℕ) :
    2 ^ (j * (j - 1) / 2) * u ^ j * f j u ≤ f 0 (2 ^ j * u) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    have ih' := ih (fun k hk => hmono k (by omega)) (fun k hk => h k (by omega)) (2 * u)
    have step := DiazModulus.nat_telescope_step (f j) (f (j + 1)) (hmono j (by omega))
      (h j (by omega)) u
    rw [tri_succ, pow_add, pow_succ, pow_succ]
    calc 2 ^ (j * (j - 1) / 2) * 2 ^ j * (u ^ j * u) * f (j + 1) u
        = 2 ^ (j * (j - 1) / 2) * (2 * u) ^ j * (u * f (j + 1) u) := by ring
      _ ≤ 2 ^ (j * (j - 1) / 2) * (2 * u) ^ j * f j (2 * u) := Nat.mul_le_mul_left _ step
      _ ≤ f 0 (2 ^ j * (2 * u)) := ih'
      _ = f 0 (2 ^ j * 2 * u) := by rw [Nat.mul_assoc]
