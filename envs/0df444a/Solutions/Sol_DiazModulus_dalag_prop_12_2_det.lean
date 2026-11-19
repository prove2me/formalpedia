-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_2_det
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:27:13.320085+00:00
-- url     : https://prove2.me/submissions/f23e8289-265c-42b4-9609-644ee8598325

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.2, the determinant of the new leading block

All entries of `A, B, C, D` lie in the field `L`, so these are images of matrices `A_L, B_L, C_L, D_L` over
`L`, and `det D_L ≠ 0` since `det D ≠ 0`. Hence `D` is invertible with inverse the image of `D_L⁻¹`, and the
Schur complement formula gives `det (xI + A, B; C, D) = det D · det (xI + A − BD⁻¹C)`. The second factor is
`det (xI − Z)` for the matrix `Z = −(A_L − B_L D_L⁻¹ C_L)` over `L`, that is, the characteristic polynomial of
`Z`, a monic (so non-zero) polynomial over `L`, evaluated at `x`. As `x` is transcendental over `L`, this
value is non-zero. So the determinant is a product of two non-zero elements of the field `K`, a unit. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K]
    (L : IntermediateField k K) (x : K) (hx : Transcendental L x) {r r' : ℕ}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin r') K) (C : Matrix (Fin r') (Fin r) K)
    (D : Matrix (Fin r') (Fin r') K) (hA : ∀ i j, A i j ∈ L) (hB : ∀ i j, B i j ∈ L)
    (hC : ∀ i j, C i j ∈ L) (hD : ∀ i j, D i j ∈ L) (hDu : IsUnit D.det) :
    IsUnit (Matrix.fromBlocks (x • (1 : Matrix (Fin r) (Fin r) K) + A) B C D).det := by
  classical
  set ι := algebraMap L K with hι
  let AL : Matrix (Fin r) (Fin r) L := fun i j => ⟨A i j, hA i j⟩
  let BL : Matrix (Fin r) (Fin r') L := fun i j => ⟨B i j, hB i j⟩
  let CL : Matrix (Fin r') (Fin r) L := fun i j => ⟨C i j, hC i j⟩
  let DL : Matrix (Fin r') (Fin r') L := fun i j => ⟨D i j, hD i j⟩
  have eA : A = AL.map ι := rfl
  have eB : B = BL.map ι := rfl
  have eC : C = CL.map ι := rfl
  have eD : D = DL.map ι := rfl
  have hDL : IsUnit DL.det := by
    rw [isUnit_iff_ne_zero] at hDu ⊢
    intro h
    exact hDu (by rw [eD, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero])
  have hmap1 : (1 : Matrix (Fin r') (Fin r') L).map ι = 1 := Matrix.map_one _ (map_zero ι) (map_one ι)
  let _ : Invertible D :=
    ⟨(DL⁻¹).map ι, by rw [eD, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hDL, hmap1],
      by rw [eD, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hDL, hmap1]⟩
  rw [Matrix.det_fromBlocks₂₂]
  have eZ : x • (1 : Matrix (Fin r) (Fin r) K) + A - B * ⅟D * C =
      Matrix.scalar _ x - (-(AL - BL * DL⁻¹ * CL)).map ι := by
    show _ = _ - _
    rw [Matrix.map_neg _ (map_neg ι), sub_neg_eq_add, Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_mul, ← eA, ← eB, ← eC,
      Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, add_sub_assoc]
    rfl
  rw [eZ, ← Matrix.eval_charpoly, Matrix.charpoly_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  refine isUnit_iff_ne_zero.2 (mul_ne_zero (isUnit_iff_ne_zero.1 hDu) fun h => hx ?_)
  exact ⟨_, (Matrix.charpoly_monic _).ne_zero, h⟩
