-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.principal_minor_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:30.545288+00:00
-- url     : https://prove2.me/submissions/2ea63692-0310-40e1-92b8-280083b1639c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]
  rw [show ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix
      (S.orderIsoOfFin hS).toEquiv (S.orderIsoOfFin hS).toEquiv
      = B.submatrix (S.orderEmbOfFin hS) id * A.submatrix id (S.orderEmbOfFin hS) from by
    ext a b
    simp [Matrix.mul_apply, Finset.coe_orderIsoOfFin_apply]]
  rw [Matrix.det_mul]
end Formalism.LatticeBaseChangeAlt
