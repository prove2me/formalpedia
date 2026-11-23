-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.det_mul_diagonal_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:00.660801+00:00
-- url     : https://prove2.me/submissions/6cdc53ff-da9d-4835-83c5-7e536f786dea

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) (d : n → R) :
    (A * diagonal d * B).det =
      ∑ J ∈ powersetCard k (univ : Finset n),
        (∏ j ∈ J, d j) * ((B * A).submatrix (Subtype.val : J → n) Subtype.val).det := by
  have h := Matrix.det_one_add_mul_comm ((X : R[X]) • (A.map C)) ((diagonal d * B).map C)
  have e1 : (X : R[X]) • A.map C * (diagonal d * B).map C
      = (X : R[X]) • (A * diagonal d * B).map C := by
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc]
  have e2 : (diagonal d * B).map C * ((X : R[X]) • A.map C)
      = (X : R[X]) • (diagonal d * (B * A)).map C := by
    rw [Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_assoc]
  rw [e1, e2] at h
  have h2 := congrArg (fun p => Polynomial.coeff p k) h
  simp only [coeff_det_one_add_X_smul_eq_sum_minors] at h2
  have hu : powersetCard k (univ : Finset (Fin k)) = {univ} := by
    simpa using Finset.powersetCard_self (univ : Finset (Fin k))
  rw [hu, sum_singleton] at h2
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => mem_univ x))]
  refine h2.trans (sum_congr rfl fun J _ => ?_)
  have : (diagonal d * (B * A)).submatrix (fun x : J => (x : n)) (fun x : J => (x : n))
      = diagonal (fun x : J => d x) * (B * A).submatrix (fun x : J => (x : n)) (fun x : J => (x : n)) := by
    ext a b; simp [diagonal_mul]
  rw [this, det_mul, det_diagonal, Finset.prod_coe_sort J d]
end Formalism.NuclearRankWeightBounds.P
