-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieF_pow_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.246409+00:00
-- url     : https://prove2.me/submissions/63b1967b-8d60-49fe-9d9c-90a757b22577

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieF_gen

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
theorem _root_.solution (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']
end Formalism.InvariantFactorPaths.KP.LL
