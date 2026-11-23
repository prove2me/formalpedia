-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.st_drop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:13.052559+00:00
-- url     : https://prove2.me/submissions/08b97ed7-33de-4a05-8ac8-4bd7de10bf17

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie

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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (t k : ℕ) (hk : k < t) :
    (List.finRange t).drop k = ⟨k, hk⟩ :: (List.finRange t).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  congr 1
  ext
  simp
end Formalism.InvariantFactorPaths.KP.LL
