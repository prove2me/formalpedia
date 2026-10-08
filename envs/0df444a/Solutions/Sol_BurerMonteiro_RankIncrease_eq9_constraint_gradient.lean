-- Prove2me | solution 1 for BurerMonteiro.RankIncrease.eq9_constraint_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:59:32.392039+00:00
-- url     : https://prove2.me/submissions/a11b1374-8cb8-40af-9f51-1510c491f047

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace A9539862Aux

open BurerMonteiro.RankIncrease

/-- The bilinear form `(X, Y) ↦ (A X) • Y`. -/
noncomputable def bil {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin r) ℝ →L[ℝ] Matrix (Fin n) (Fin r) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => frobCLM (A * X)
      map_add' := fun X Y => by
        ext D
        simp [frobCLM, frob, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun c X => by
        ext D
        simp [frobCLM, frob, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] }

lemma bil_apply {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Matrix (Fin n) (Fin r) ℝ) :
    bil A X Y = frob (A * X) Y := rfl

end A9539862Aux

open BurerMonteiro.RankIncrease Matrix Matrix.Norms.Frobenius in
theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : ∀ i, (A i).IsSymm) {r : ℕ} (hr0 : 0 < r) (hrn : r ≤ n)
    (i : Fin m) (R : Matrix (Fin n) (Fin r) ℝ) :
    HasFDerivAt (fun R' : Matrix (Fin n) (Fin r) ℝ => frob (A i) (R' * R'ᵀ) - b i)
      (frobCLM ((2 : ℝ) • (A i * R))) R := by
  have hfun : (fun R' : Matrix (Fin n) (Fin r) ℝ => frob (A i) (R' * R'ᵀ) - b i)
      = fun R' => A9539862Aux.bil (A i) R' R' - b i := by
    funext R'
    rw [A9539862Aux.bil_apply]
    simp only [frob, Matrix.transpose_mul]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hfun]
  have h := (A9539862Aux.bil (A i)).hasFDerivAt_of_bilinear
    (hasFDerivAt_id (𝕜 := ℝ) R) (hasFDerivAt_id (𝕜 := ℝ) R)
  refine (h.sub_const (b i)).congr_fderiv ?_
  ext D
  have hs : (A i)ᵀ = A i := hA i
  change A9539862Aux.bil (A i) R D + A9539862Aux.bil (A i) D R
    = frobCLM ((2 : ℝ) • (A i * R)) D
  show frob (A i * R) D + frob (A i * D) R = frob ((2 : ℝ) • (A i * R)) D
  have key : ((Dᵀ * A i) * R).trace = (Rᵀ * A i * D).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hs, Matrix.mul_assoc]
  unfold frob
  simp only [Matrix.transpose_mul, hs, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]
  rw [key]
  ring
