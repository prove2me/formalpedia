-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_Pt_param
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:49.139871+00:00
-- url     : https://prove2.me/submissions/c3e7d25b-be08-49cc-bd72-287a0056ac62

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_lettersAt_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_lettersAt_pos_succ


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
theorem _root_.solution (hB : D.BlockOK) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (i : Fin D.T.t) (h : j i = j' i)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : Pt p D j jp i x = Pt p D j' jp' i x := by
  unfold Pt
  rw [deg_lettersAt_pos hB j jp, deg_lettersAt_pos_succ hB j jp, deg_lettersAt_pos hB j' jp', deg_lettersAt_pos_succ hB j' jp', h]
end Formalism.InvariantFactorPaths.KP.LL
