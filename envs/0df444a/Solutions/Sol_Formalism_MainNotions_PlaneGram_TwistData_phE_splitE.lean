-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.phE_splitE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:28.038439+00:00
-- url     : https://prove2.me/submissions/76adcc2a-48a1-4967-88f3-ca58c7bba371

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_splitE_mtp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inr


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
theorem _root_.solution (p : ℕ) (ζ : D.EM) : D.phE p (D.splitE p ζ) = D.phE p ζ := by
  ext ⟨i, a⟩
  rcases i with b | t
  · rw [phE_apply_inl, phE_apply_inl, splitE_mb]
  · rw [phE_apply_inr, phE_apply_inr, splitE_mlab, splitE_mw, splitE_mtp, mul_add]
    have := Nat.mod_add_div (ζ (D.mlab t, a)) (D.P p t)
    linarith
end Formalism.MainNotions.PlaneGram.TwistData
