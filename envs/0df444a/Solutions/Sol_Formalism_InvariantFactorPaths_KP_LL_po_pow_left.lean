-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_pow_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.535795+00:00
-- url     : https://prove2.me/submissions/523dc7f8-0be4-49e1-a3a7-083bcff9386d

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
theorem _root_.solution {σ τ : Type} (f : τ → σ) (hf : Function.Injective f) (u : τ)
    (y : MvPolynomial τ ℚ_[p]) {g : MvPolynomial σ ℚ_[p]} (hg : pderiv (f u) g = 0) (k : ℕ) :
    (po_d (f u) ^ k) (rename f y * g) = rename f ((po_d u ^ k) y) * g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
    show pderiv (f u) (_ * g) = rename f (pderiv u _) * g
    rw [pderiv_mul, hg, mul_zero, add_zero, pderiv_rename hf]
end Formalism.InvariantFactorPaths.KP.LL
