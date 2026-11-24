-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_branchingAlg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:15.68122+00:00
-- url     : https://prove2.me/submissions/87dab804-6573-4873-8055-9873651e7581

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_box_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.Decomp → Qr.CapIndep → Qr.IrredCap → Qr.BranchingAlg := by
  intro hD hCI hIC V _ _ _ n E β L H
  obtain ⟨hne, htop⟩ := hD V n E β L H
  refine ⟨?_, fun M => ⟨hne M.1 M.2, fun S' hS' hst => hIC V n E β L H M.1 M.2 S' hS' hst⟩⟩
  have hind := StrictBoxOrder.box_indep hCI (subA E) β L
  have hsup : (⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1)) = ⊤ :=
    iSup_subtype.trans htop
  first
  | exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  | exact DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top hind hsup
end Formalism.FourierDecayAlt.P
