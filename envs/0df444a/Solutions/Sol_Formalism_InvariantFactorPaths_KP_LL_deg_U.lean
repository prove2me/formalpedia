-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.deg_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:30.966257+00:00
-- url     : https://prove2.me/submissions/0205d946-20fa-4d60-a17b-a4e143ef9b07

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pos_lt_u

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
variable {N r : ℕ} (D : BlockData N)
variable {D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp
end Formalism.InvariantFactorPaths.KP.LL
