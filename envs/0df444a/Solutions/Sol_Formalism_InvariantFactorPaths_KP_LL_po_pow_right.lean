-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_pow_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:19.916172+00:00
-- url     : https://prove2.me/submissions/35381b4a-53f2-4546-bfdb-46f6d2ddf1d8

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {σ : Type} (v : σ) {a : MvPolynomial σ ℚ_[p]} (ha : pderiv v a = 0)
    (g : MvPolynomial σ ℚ_[p]) (k : ℕ) : (po_d v ^ k) (a * g) = a * (po_d v ^ k) g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv v (a * _) = a * pderiv v _
    rw [pderiv_mul, ha, zero_mul, zero_add]
end Formalism.InvariantFactorPaths.KP.LL
