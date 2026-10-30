-- Prove2me | solution 1 for DiazModulus.thetaN_ge_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T06:18:04.427979+00:00
-- url     : https://prove2.me/submissions/f225fc3d-d5ca-4aa0-95fa-2d155fd3c40e

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A(L − Aⁿ) ≤ Θₙ(L)

Θₙ(L) is the least total degree `∑ₗ |κ'(l)|` of `L` distinct multi-indices in `ℕⁿ`. The set of
admissible sums is non-empty when `n ≥ 1` (take `κ'(l) = (l, …, l)`), so it suffices to bound
every admissible sum from below. Fix an injective `κ'`. The indices `l` whose multi-index lies in
the box `{0, …, A − 1}ⁿ` are at most `Aⁿ` in number, since `κ'` maps them injectively into that
box (`Fintype.piFinset`, of cardinality `Aⁿ`). Every other `l` has a coordinate `≥ A`, so its
degree is at least `A`. Hence the total degree is at least `A` times the number of indices
outside the box, which is at least `L − Aⁿ`.
-/

namespace C14_A1
open DiazModulus

/-- Lower bound for one injective family. -/
theorem sum_ge (n L A : ℕ) (κ' : Fin L → (Fin n → ℕ)) (hκ : Function.Injective κ') :
    A * (L - A ^ n) ≤ ∑ l, ∑ i, κ' l i := by
  classical
  set S : Finset (Fin L) := Finset.univ.filter (fun l => ∀ i, κ' l i < A) with hS
  have hcardS : S.card ≤ A ^ n := by
    have h := Finset.card_le_card_of_injOn κ'
      (s := S) (t := Fintype.piFinset (fun _ : Fin n => Finset.range A))
      (fun l hl => by
        have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
        simpa [Fintype.mem_piFinset] using hl')
      (hκ.injOn)
    simpa [Fintype.card_piFinset] using h
  have hcompl : L - A ^ n ≤ Sᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  have hlow : ∀ l ∈ Sᶜ, A ≤ ∑ i, κ' l i := by
    intro l hl
    simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall, not_lt] at hl
    obtain ⟨i, hi⟩ := hl
    exact hi.trans (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  calc A * (L - A ^ n) ≤ A * Sᶜ.card := Nat.mul_le_mul_left _ hcompl
    _ = ∑ l ∈ Sᶜ, A := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ l ∈ Sᶜ, ∑ i, κ' l i := Finset.sum_le_sum hlow
    _ ≤ ∑ l, ∑ i, κ' l i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

end C14_A1

open DiazModulus C14_A1 in
theorem solution (n L A : ℕ) (hn : 1 ≤ n) :
    A * (L - A ^ n) ≤ sInf {S | ∃ κ' : Fin (L) → (Fin n → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} := by
  apply le_csInf
  · refine ⟨_, fun l : Fin L => fun _ : Fin n => (l : ℕ), ?_, rfl⟩
    intro a b h
    have := congrFun h ⟨0, hn⟩
    exact Fin.ext this
  · rintro S ⟨κ', hκ, rfl⟩
    exact sum_ge n L A κ' hκ
