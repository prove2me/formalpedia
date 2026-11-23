-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_PplusL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:47.259185+00:00
-- url     : https://prove2.me/submissions/1fb66093-f952-474b-ad29-cf0bf2e1b39c

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_tiePL_apply

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
theorem _root_.solution (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    cmPplusL p D jp x = Pplus p D jp x := by
  unfold cmPplusL
  rw [cm_tiePL_apply]
  rfl
end Formalism.InvariantFactorPaths.KP.LL
