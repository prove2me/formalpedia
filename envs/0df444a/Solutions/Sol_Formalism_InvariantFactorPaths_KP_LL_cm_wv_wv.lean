-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_wv_wv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:34.473165+00:00
-- url     : https://prove2.me/submissions/28327ce1-345d-404c-9a98-8b846cadc0f9

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_pos_val
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_inj


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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) {i k : Fin D.T.t} (h : i ≠ k) (c d : Fin r) : wv D i d ≠ wv D k c := by
  intro h'
  simp only [wv, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_pos_val hB] at this
  exact h (pos_inj hB this)
end Formalism.InvariantFactorPaths.KP.LL
