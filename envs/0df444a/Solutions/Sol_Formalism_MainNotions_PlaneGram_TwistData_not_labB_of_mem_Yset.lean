-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.not_labB_of_mem_Yset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:46.380272+00:00
-- url     : https://prove2.me/submissions/89bce132-6fdd-49a2-afc4-a36daf176c5b

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
theorem _root_.solution {j : Fin D.J} {m : Fin D.r} {i : D.ML} (hi : i ∈ D.Yset j m) :
    ¬ D.labB i = true := by
  simp only [Yset, wSet, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with (⟨m', _, rfl⟩ | ⟨b, _, rfl⟩) | ⟨m', _, rfl⟩ <;> simp [labB, mw, mb, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
