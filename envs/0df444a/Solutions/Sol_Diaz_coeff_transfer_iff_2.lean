-- Prove2me | solution 2 for Diaz.coeff_transfer_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:34:23.577979+00:00
-- url     : https://prove2.me/submissions/a7cef5b2-ada5-468f-8d63-9d23360b9156

/-
`Diaz.coeff_transfer_iff` through `Diaz.coeff_transfer`.

The two nodes state the same forward identity; they differ only in the index
types, `Fin m` / `Fin n` in `coeff_transfer` against arbitrary `Fintype`s here.
The generalisation is a reindexing along `Fintype.equivFin` and carries no
mathematical content, which is precisely why it should be cited rather than
reproved: the previous accepted proof of this node re-derived the identity from
`map_sum` and `map_mul`, so `Diaz.coeff_transfer` had no children at all.

The second clause — that `Φ` detects vanishing exactly — is the half that needs
injectivity of `Φ`, which no ring homomorphism out of a field can fail; it stays
here, since `coeff_transfer` does not carry it.
-/
import Mathlib
import Theorems.Thm_Diaz_coeff_transfer

open ComplexConjugate

theorem solution {K : Subfield ℂ} {m n : Type*} [Fintype m] [Fintype n]
    (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j ∧
      ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by
  classical
  have re : ∀ N : m → n → ℂ,
      ∑ i, ∑ j, w ((Fintype.equivFin m).symm i)
          * N ((Fintype.equivFin m).symm i) ((Fintype.equivFin n).symm j)
          * v ((Fintype.equivFin n).symm j)
        = ∑ i, ∑ j, w i * N i j * v j := by
    intro N
    rw [← Equiv.sum_comp (Fintype.equivFin m).symm (fun i => ∑ j, w i * N i j * v j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp (Fintype.equivFin n).symm
      (fun j => w ((Fintype.equivFin m).symm i) * N ((Fintype.equivFin m).symm i) j * v j)
  have key : Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j := by
    rw [← re (fun i j => M i j), ← re (fun i j => Φ (M i j))]
    exact Diaz.coeff_transfer Φ hK
      (Matrix.of fun i j => M ((Fintype.equivFin m).symm i) ((Fintype.equivFin n).symm j))
      (fun i => w ((Fintype.equivFin m).symm i)) (fun j => v ((Fintype.equivFin n).symm j))
      (fun i => hw _) (fun j => hv _)
  refine ⟨key, ?_, ?_⟩
  · intro h0; rw [← key, h0, map_zero]
  · intro h0; refine Φ.injective ?_; rw [key, h0, map_zero]
