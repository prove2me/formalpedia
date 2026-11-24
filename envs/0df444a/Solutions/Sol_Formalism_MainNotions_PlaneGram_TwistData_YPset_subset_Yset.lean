-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.YPset_subset_Yset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:13.762927+00:00
-- url     : https://prove2.me/submissions/cc6d01cc-a186-43ab-a850-8e1130a9d4a1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (j : Fin D.J) (m : Fin D.r) : D.YPset j m ⊆ D.Yset j m := by
  intro i hi
  simp only [YPset, Yset, Finset.mem_union] at hi ⊢
  tauto
end Formalism.MainNotions.PlaneGram.TwistData
