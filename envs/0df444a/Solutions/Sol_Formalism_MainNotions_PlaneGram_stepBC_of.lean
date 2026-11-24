-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.stepBC_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:34.191484+00:00
-- url     : https://prove2.me/submissions/e1880b51-0fee-4a8c-bd5e-a2ec45aad307

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets

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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hB : StepB K v p C0) (hC : StepC K v p) : StepBC K v p C0 := by
  intro hD D hV hc F hF hF0
  obtain ⟨Gt, hGt, hval, hle⟩ := hB hD D hV hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZph, hZv⟩ := hC hD D hV.1 hV.2.1 (fun j m => D.thl j m - 6 * D.c) Gt hGt hval
  refine ⟨Z, hZi, hZg, hZv, ?_⟩
  unfold TwistData.abelian₂
  rw [hZph]; exact hle
end Formalism.MainNotions.PlaneGram
