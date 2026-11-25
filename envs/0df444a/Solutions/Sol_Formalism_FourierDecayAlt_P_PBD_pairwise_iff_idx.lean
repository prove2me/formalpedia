-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.pairwise_iff_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:05.030726+00:00
-- url     : https://prove2.me/submissions/f0f9f879-9159-474b-9e83-6f0e3c6a1626

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_sep_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (L : List C.Letter) :
    L.Pairwise Sep ↔ ∀ (j j' : ℕ) (hj : j < L.length) (hj' : j' < L.length), j ≠ j' → Sep (L[j]'hj) (L[j']'hj') := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h j j' hj hj' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h j j' hj hj' hlt
    · exact sep_symm (h j' j hj' hj hlt)
  · intro h j j' hj hj' hlt
    exact h j j' hj hj' (ne_of_lt hlt)
end Formalism.FourierDecayAlt.P.PBD
