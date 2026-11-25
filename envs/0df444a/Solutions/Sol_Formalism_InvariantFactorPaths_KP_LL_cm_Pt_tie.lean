-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.cm_Pt_tie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:27.440967+00:00
-- url     : https://prove2.me/submissions/a222ee30-4328-4938-8b1f-12de60fd0c6b

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Fpow_P
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_wv_wv
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_ev_ev
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_wv_ev

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
theorem _root_.solution (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) {i k : Fin D.T.t} (h : i ≠ k)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i x) = Pt p D j jp i ((tieF (wv D k) (ev D k) ^ m) x) :=
  cm_Fpow_P (wv D k) (ev D k) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wv hB h c d, fun d => (cm_wv_ev hB k i d c).symm⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_ev hB i k c d, fun d => cm_ev_ev hB h c d⟩) m x
end Formalism.InvariantFactorPaths.KP.LL
