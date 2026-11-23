-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_PLL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:45.144274+00:00
-- url     : https://prove2.me/submissions/2879203f-e299-4f5a-bd55-31057fb92190

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
theorem _root_.solution (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : cmPLL p D L j jp x = PL p D L j jp x := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have h1 : cmPLL (r := r) p D (i :: L) j jp = cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
        ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
        (D.T.z i) * cmPLL p D L j jp := rfl
    rw [h1, Module.End.mul_apply, ih, cm_tiePL_apply]
    rfl
end Formalism.InvariantFactorPaths.KP.LL
