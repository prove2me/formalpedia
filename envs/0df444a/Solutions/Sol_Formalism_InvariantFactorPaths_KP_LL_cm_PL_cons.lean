-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_PL_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:49.198065+00:00
-- url     : https://prove2.me/submissions/cc3c82a9-6d2a-4f67-848c-0921848f0f2f

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds

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
theorem _root_.solution (i : Fin D.T.t) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : PL p D (i :: L) j jp x = Pt p D j jp i (PL p D L j jp x) := rfl
end Formalism.InvariantFactorPaths.KP.LL
