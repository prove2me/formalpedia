-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.lattice_plus_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:46.481852+00:00
-- url     : https://prove2.me/submissions/7a12c536-816e-44bb-8e11-73d2a6cc8589

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_Fsum
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_coord
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv


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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : LatPlus := by
  intro p _ N r _ D hB hU j jp m L hmL x hx
  classical
  have hcomm : ∀ a b : Fin r, Commute (po_d (p := p) (wU D a) ∘ₗ po_d (xiVar N r D.T.t a))
      (po_d (wU D b) ∘ₗ po_d (xiVar N r D.T.t b)) := by
    intro a b
    simp only [← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have h := po_Fsum (fun c : Fin r => po_d (p := p) (wU D c) ∘ₗ po_d (xiVar N r D.T.t c)) hcomm
    (fun l => Lat p D (r := r) j l) (fun a k l x hx => po_coord hU j a k l x hx) L m hmL Finset.univ
    m le_rfl jp x hx
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h
end Formalism.InvariantFactorPaths.KP.LL
