-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.notSegL_of_mem_TLset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:43.588796+00:00
-- url     : https://prove2.me/submissions/76e007d8-21d9-4204-9882-3da4abdb36f3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mlab

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
theorem _root_.solution {j j' : Fin D.J} (h : j' ≠ j) (m : Fin D.r) {i : D.ML}
    (hi : i ∈ D.TLset j' m) : ¬ D.SegL j i := by
  simp only [TLset, Finset.mem_union, Finset.mem_image] at hi
  rcases hi with ⟨b, hb, rfl⟩ | ⟨m', _, rfl⟩
  · simp [LLj] at hb
    exact D.notSegL_mb (by rw [hb]; exact h)
  · exact D.notSegL_mlab m' h
end Formalism.MainNotions.PlaneGram.TwistData
