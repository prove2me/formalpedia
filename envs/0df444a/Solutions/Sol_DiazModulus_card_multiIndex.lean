-- Prove2me | solution 1 for DiazModulus.card_multiIndex
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:42.448965+00:00
-- url     : https://prove2.me/submissions/17c2296c-426b-48d8-b489-525f7e131485

import Mathlib

open Complex ComplexConjugate

/-! # Counting multi-indices of bounded length
The multi-indices `α : Fin n → {0, …, S}` with `Σ α ≤ S` are in bijection with the
tuples `β : Fin (n + 1) → ℕ` with `Σ β = S`: prepend the slack `S − Σ α`, and conversely drop
the first entry (each other entry is at most `S` since it is bounded by the total).  Those
tuples are the multisets of size `S` on `Fin (n + 1)` (Mathlib's `Sym.equivNatSumOfFintype`),
which stars and bars counts as `C(n + S, S)` (`Sym.card_sym_eq_choose`); symmetry of the
binomial coefficient gives `C(S + n, n)`. -/

namespace C13_W4

/-- Prepending the slack: bounded multi-indices ≃ tuples of length `n + 1` summing to `S`. -/
def slackEquiv (n S : ℕ) :
    {α : Fin n → Fin (S + 1) // ∑ i, (α i : ℕ) ≤ S} ≃ {β : Fin (n + 1) → ℕ // ∑ i, β i = S} where
  toFun α := ⟨Fin.cons (S - ∑ i, (α.1 i : ℕ)) (fun i => (α.1 i : ℕ)), by
    have := α.2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega⟩
  invFun β := ⟨fun i => ⟨β.1 i.succ, by
      have h1 : β.1 i.succ ≤ ∑ j, β.1 j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (β.1 j)) (Finset.mem_univ _)
      have := β.2
      omega⟩, by
    have := β.2
    rw [Fin.sum_univ_succ] at this
    simp only
    omega⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    simp
  right_inv β := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have := β.2
      rw [Fin.sum_univ_succ] at this
      simp only [Fin.cons_zero]
      omega
    · simp

end C13_W4

open C13_W4 in
theorem solution (n S : ℕ) :
    (Finset.univ.filter fun α : Fin n → Fin (S + 1) => ∑ i, (α i : ℕ) ≤ S).card = (S + n).choose n := by
  classical
  rw [← Fintype.card_subtype,
    Fintype.card_congr ((slackEquiv n S).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) S).symm),
    Sym.card_sym_eq_choose,
    Fintype.card_fin, show n + 1 + S - 1 = S + n by omega, Nat.choose_symm_add]
