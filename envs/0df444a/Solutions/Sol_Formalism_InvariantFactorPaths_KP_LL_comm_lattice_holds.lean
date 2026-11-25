-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.comm_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:45:15.819369+00:00
-- url     : https://prove2.me/submissions/a39c823c-2523-44fb-b8d1-14a87e6ffbfd

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Pt_tie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Pt_plus

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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : CommPL := by
  intro p _ N r _ D hB L j jp m x
  induction L with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons i L ih =>
    refine ⟨fun k hk => ?_, ?_⟩
    · have hki : i ≠ k := fun h => hk (by simp [h])
      have hkL : k ∉ L := fun h => hk (by simp [h])
      show (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x))
      rw [cm_Pt_tie hB j jp m hki, ih.1 k hkL]
    · show (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x))
      rw [cm_Pt_plus hB j jp m i, ih.2]
end Formalism.InvariantFactorPaths.KP.LL
