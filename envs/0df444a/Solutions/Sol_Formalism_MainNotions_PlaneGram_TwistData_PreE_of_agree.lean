-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.PreE.of_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:36.603385+00:00
-- url     : https://prove2.me/submissions/c870d992-c58f-4fb0-8424-35d7b28da592

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mlab
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_notSegL_mtp
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2

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
namespace PreE
theorem _root_.solution {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PreE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PreE j' ζ' := by
  obtain ⟨h1, h2, h3⟩ := hζ
  refine ⟨fun b hb => ?_, fun m => ?_, fun m a => ?_⟩
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mb (by rw [hb]; exact h)))]
    exact h1 b hb
  · rw [D.ldeg_congr' (hag _ (D.notSegL_mlab m h))]
    exact h2 m
  · rw [hag _ (D.notSegL_mtp m h)]
    exact h3 m a
end PreE
end Formalism.MainNotions.PlaneGram.TwistData
