-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.update_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:15.754417+00:00
-- url     : https://prove2.me/submissions/3a14b603-bee1-4910-9863-3963b67678cd

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds

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
omit [NeZero r]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp; ring
  · simp [hk]
end Formalism.InvariantFactorPaths.KP.LL
