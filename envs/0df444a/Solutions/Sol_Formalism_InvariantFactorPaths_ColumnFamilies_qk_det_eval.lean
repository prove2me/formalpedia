-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_det_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.535525+00:00
-- url     : https://prove2.me/submissions/bb9c4889-9a54-40a3-bbd2-d7aa0d3a9f52

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (hdeg : ∀ i, (p i).natDegree ≤ i) :
    (Matrix.of fun i j => (p j).eval (v i)).det = (Matrix.vandermonde v).det * ∏ i, (p i).coeff i := by
  have h : (Matrix.of fun i j => (p j).eval (v i)) =
      Matrix.vandermonde v * Matrix.of fun (i j : Fin n) => (p j).coeff i := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (hdeg j) j.2),
      ← Fin.sum_univ_eq_sum_range (fun k => (p j).coeff k * v i ^ k)]
    refine sum_congr rfl fun k _ => ?_
    simp [Matrix.vandermonde_apply, mul_comm]
  rw [h, Matrix.det_mul, Matrix.det_of_isUpperTriangular (Matrix.matrixOfPolynomials_blockTriangular p hdeg)]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
