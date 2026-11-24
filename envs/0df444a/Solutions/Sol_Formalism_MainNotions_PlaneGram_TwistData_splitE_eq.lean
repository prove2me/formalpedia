-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.splitE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:33.865036+00:00
-- url     : https://prove2.me/submissions/268c4ff6-5b20-45c6-adfa-81bb8376c34d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mtp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply


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
theorem _root_.solution (p : ℕ) (α : D.EM) :
    D.splitE p α = eIn (fun i => D.labB i = true) α + D.splitE p (eOut (fun i => D.labB i = true) α) := by
  ext ⟨i, a⟩
  rw [Finsupp.add_apply]
  rcases i with b | t | t | t
  · show D.splitE p α (D.mb b, a) = eIn _ α (D.mb b, a) + D.splitE p (eOut _ α) (D.mb b, a)
    rw [splitE_mb, splitE_mb, eIn_apply, eOut_apply]
    simp [labB, mb]
  · show D.splitE p α (D.mlab t, a) = eIn _ α (D.mlab t, a) + D.splitE p (eOut _ α) (D.mlab t, a)
    rw [splitE_mlab, splitE_mlab, eIn_apply, eOut_apply]
    simp [labB, mlab]
  · show D.splitE p α (D.mw t, a) = eIn _ α (D.mw t, a) + D.splitE p (eOut _ α) (D.mw t, a)
    rw [splitE_mw, splitE_mw, eIn_apply, eOut_apply, eOut_apply]
    simp [labB, mw, mlab]
  · show D.splitE p α (D.mtp t, a) = eIn _ α (D.mtp t, a) + D.splitE p (eOut _ α) (D.mtp t, a)
    rw [splitE_mtp, splitE_mtp, eIn_apply, eOut_apply]
    simp [labB, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
