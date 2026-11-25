-- Prove2me | solution 1 for BorderDiffEq.lemma_4_23
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-25T07:06:36.933339+00:00
-- url     : https://prove2.me/submissions/1d4adc3e-f33c-4470-9c95-f5ffa5f153ea

import Mathlib
import Definitions.Def_BorderDiffEq_signedMinor

open BorderDiffEq
/-- The `(n+1) × (n+1)` square matrix obtained by duplicating row `A i` of `A` as its `0`-th row:
`dupRow0 A i` has row `0` = row `A i` and row `k.succ` = row `A k` of `A`. -/
def dupRow0 {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R) (i : Fin n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun k l => if hk : k = 0 then A i l else A (k.pred hk) l

/-- Removing row `0` from the duplicated-row matrix `dupRow0 A i` recovers `A` itself, so the
`j`-th column minor of `dupRow0 A i` equals the `j`-th column minor of `A`. -/
-- riskiest
theorem dupRow0_submatrix {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R)
    (i : Fin n) (j : Fin (n + 1)) :
    (dupRow0 A i).submatrix Fin.succ j.succAbove = A.submatrix id j.succAbove := by
  ext k l
  simp [dupRow0]

/-- In `dupRow0 A i` the duplicated row appears twice: row `0` and row `i.succ` are both `A i`. -/
theorem dupRow0_dup_rows {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) R)
    (i : Fin n) : (dupRow0 A i) 0 = (dupRow0 A i) (i.succ) := by
  ext j
  simp [dupRow0]

/-- **Lemma 4.23 (signed maximal minors give a kernel vector)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.23, p.30). Let `A` be an `n × (n+1)` matrix and `A_j` the `n × n` matrix
obtained by removing the `j`-th column. For `v_j := (-1)^{j+1} det(A_j)` (1-based `j`), `A v = 0`.

**Formalization Note.** Entries in any commutative ring `R` (the paper: a field `F`). Columns are
0-based, so `v = signedMinor A` with `v_j = (-1)^j det(A with column j removed)`, which is the
paper's sign `(-1)^{j'+1}` for `j' = j + 1`. The hypothesis "of rank `n`" is dropped: the identity
holds for every matrix. -/
theorem solution (R : Type) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin (n + 1)) R) :
    A.mulVec (signedMinor A) = 0 := by
  ext i
  have hB : (dupRow0 A i).det = 0 :=
    Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i) (dupRow0_dup_rows A i)
  calc
    A.mulVec (signedMinor A) i = ∑ j : Fin (n + 1), A i j * (signedMinor A) j := by
      rw [Matrix.mulVec_apply_eq_sum]
    _ = ∑ j : Fin (n + 1), A i j * (-1 : R) ^ (j : ℕ) * (A.submatrix id j.succAbove).det := by
      apply Finset.sum_congr rfl
      intro j _
      simp [signedMinor]
      ring
    _ = ∑ j : Fin (n + 1), (-1 : R) ^ (j : ℕ) * (dupRow0 A i) 0 j *
        ((dupRow0 A i).submatrix Fin.succ j.succAbove).det := by
      apply Finset.sum_congr rfl
      intro j _
      have h0 : (dupRow0 A i) 0 j = A i j := by simp [dupRow0]
      rw [h0, dupRow0_submatrix A i j]
      ring
    _ = (dupRow0 A i).det := (Matrix.det_succ_row_zero (dupRow0 A i)).symm
    _ = 0 := hB
