-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_Y_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.59874+00:00
-- url     : https://prove2.me/submissions/52961dde-1d70-42ad-af4c-feb0120a8f3f

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
variable {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hU : HypU p (r := r) D) (c : Fin r) (j : Fin D.T.t → ℕ) :
    ∀ k (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (po_d (D.uPos, c) ^ k) y ∈ Y p (r := r) (D.lettersAt j (jp + k)) D.T.J D.T.thr := by
  intro k
  induction k with
  | zero => intro jp y hy; rw [pow_zero, Module.End.one_apply, add_zero]; exact hy
  | succ k ih =>
    intro jp y hy
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact hU j (jp + k) c _ (ih jp y hy)
end Formalism.InvariantFactorPaths.KP.LL
