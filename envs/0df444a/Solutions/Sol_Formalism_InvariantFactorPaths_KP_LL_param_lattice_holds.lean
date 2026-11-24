-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.param_lattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:18.283027+00:00
-- url     : https://prove2.me/submissions/b47308c8-dbcb-478d-906a-60ae272afc5c

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeLinearHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_Pt_param
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PL_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_cm_PL_cons

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
theorem _root_.solution : ParamPL := by
  intro p _ N r _ D hB L j j' jp jp' x h
  induction L with
  | nil => rw [cm_PL_nil, cm_PL_nil]
  | cons i L ih =>
    rw [cm_PL_cons, cm_PL_cons, ih (fun a ha => h a (by simp [ha])), cm_Pt_param hB j j' jp jp' i (h i (by simp))]
end Formalism.InvariantFactorPaths.KP.LL
