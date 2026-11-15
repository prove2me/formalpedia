-- Prove2me | solution 1 for DiazModulus.matrix_rank_le_of_zero_block
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:49.046205+00:00
-- url     : https://prove2.me/submissions/a28ffdc7-de0e-4288-83af-904e2f34fd54

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The rank of a matrix with a zero block

Let `N` be a `d × ℓ` matrix over a field with `Nᵢⱼ = 0` for `i < d'` and `j ≥ ℓ'`. The rank of `N` is the
dimension of its row space. Each of the first `d'` rows has zero coordinates beyond `ℓ'`, so it is a
combination of the unit vectors `e_j` with `j < ℓ'`; that span has dimension at most `ℓ'`. The remaining
`d − d'` rows span a space of dimension at most `d − d'`. The row space lies in the sum of these two spaces,
so `rank N ≤ ℓ' + (d − d')`, that is `rank N + d' ≤ d + ℓ'`. -/

namespace RC3_ZB

theorem card_lt_le (l l' : ℕ) : Fintype.card {j : Fin l // j.val < l'} ≤ l' := by
  have h := Fintype.card_le_of_injective (fun j : {j : Fin l // j.val < l'} => (⟨j.1.val, j.2⟩ : Fin l'))
    (fun a b hab => Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hab)))
  simpa using h

theorem card_ge_le (d d' : ℕ) : Fintype.card {i : Fin d // d' ≤ i.val} ≤ d - d' := by
  have h := Fintype.card_le_of_injective
    (fun i : {i : Fin d // d' ≤ i.val} => (⟨i.1.val - d', by have := i.1.2; have := i.2; omega⟩ : Fin (d - d')))
    (fun a b hab => by
      have h1 := congrArg Fin.val hab
      simp only at h1
      have := a.2; have := b.2
      exact Subtype.ext (Fin.ext (by omega)))
  simpa using h

end RC3_ZB

open RC3_ZB in
theorem solution {K : Type*} [Field K] {d l : ℕ} (N : Matrix (Fin d) (Fin l) K)
    (d' l' : ℕ) (hz : ∀ (i : Fin d) (j : Fin l), i.val < d' → l' ≤ j.val → N i j = 0) (hd' : d' ≤ d) :
    N.rank + d' ≤ d + l' := by
  classical
  set C : Submodule K (Fin l → K) := Submodule.span K
    (Set.range fun j : {j : Fin l // j.val < l'} => fun k : Fin l => if j.1 = k then (1 : K) else 0)
  set B : Submodule K (Fin l → K) := Submodule.span K
    (Set.range fun i : {i : Fin d // d' ≤ i.val} => N.row i.1)
  have hle : Submodule.span K (Set.range N.row) ≤ C ⊔ B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < d'
    · apply Submodule.mem_sup_left
      rw [pi_eq_sum_univ (N.row i)]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j.val < l'
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
      · simp [Matrix.row, hz i j hi (by omega)]
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩)
  have hC : Module.finrank K C ≤ l' := (finrank_range_le_card _).trans (card_lt_le l l')
  have hB : Module.finrank K B ≤ d - d' := (finrank_range_le_card _).trans (card_ge_le d d')
  have h1 := (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank C B)
  rw [← Matrix.rank_eq_finrank_span_row] at h1
  omega
