-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_Pt_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:28.671403+00:00
-- url     : https://prove2.me/submissions/45959c2f-f9c8-4de7-b77f-05ca37334cf9

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Fpow_P
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_wv_wU
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_ev_wU
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_ne_xi
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_ne_xi


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
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) (i : Fin D.T.t)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i x) =
      Pt p D j jp i ((tieF (wU D) (xiVar N r D.T.t) ^ m) x) :=
  cm_Fpow_P (wU D) (xiVar N r D.T.t) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wU hB i c d, fun d => cm_ev_wU hB i c d⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => wv_ne_xi hB i d c, fun d => ev_ne_xi hB i d c⟩) m x
end Formalism.InvariantFactorPaths.KP.LL
