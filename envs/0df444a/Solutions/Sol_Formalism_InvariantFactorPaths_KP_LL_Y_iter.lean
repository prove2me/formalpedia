-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.Y_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.243834+00:00
-- url     : https://prove2.me/submissions/107031d9-bf81-49ce-8ad8-9ddde7660150

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_update_single

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
theorem _root_.solution (hF : HypJoin p (r := r) D) (i : Fin D.T.t) :
    ∀ m (j : Fin D.T.t → ℕ) (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y ∈
        Y p (r := r) (D.lettersAt (j + Pi.single i m) jp) D.T.J D.T.thr := by
  intro m
  induction m with
  | zero =>
    intro j jp y hy
    have h0 : j + Pi.single i 0 = j := by simp
    rw [h0, pow_zero, Module.End.one_apply]
    exact hy
  | succ m ih =>
    intro j jp y hy
    have h := hF _ jp i _ (ih j jp y hy)
    rw [update_single] at h
    rw [pow_succ', Module.End.mul_apply]
    exact h
end Formalism.InvariantFactorPaths.KP.LL
