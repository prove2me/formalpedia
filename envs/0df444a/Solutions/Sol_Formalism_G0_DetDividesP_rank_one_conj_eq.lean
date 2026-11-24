-- Prove2me | solution 1 for Formalism.G0.DetDividesP.rank_one_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:23.953825+00:00
-- url     : https://prove2.me/submissions/f842c7df-9dd8-4914-98f8-80d77fe2275a

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
variable {L : Type} [Field L]
namespace Formalism.G0.DetDividesP
theorem _root_.solution (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)) *
      (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (Pi.single i 1)) *
      (1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1))
      = 1 - Matrix.vecMulVec (Pi.single i (1 : L)) φ := by
  set e : Fin r → L := Pi.single i 1 with he
  set E := Matrix.vecMulVec e (φ - e) with hE
  set Q := Matrix.vecMulVec e e with hQ
  have hv : (φ - e) ⬝ᵥ e = 0 := by
    rw [he, dotProduct_single]; simp [hφ]
  have hee : e ⬝ᵥ e = 1 := by rw [he, dotProduct_single]; simp
  have hEQ : E * Q = 0 := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hEE : E * E = 0 := by rw [hE, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hQE : Q * E = E := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
  have hsum : Q + E = Matrix.vecMulVec e φ := by
    ext a b; simp [hQ, hE, Matrix.vecMulVec_apply]; ring
  have h1 : (1 - E) * (1 - Q) = 1 - Q - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hEQ]; abel
  rw [h1, mul_add, mul_one, sub_mul, sub_mul, one_mul, hQE, hEE, ← hsum]
  abel
end Formalism.G0.DetDividesP
