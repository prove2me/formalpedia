-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.monomial_mem_PolK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:07:35.134424+00:00
-- url     : https://prove2.me/submissions/07f41693-8ce2-4595-8a92-a45775bba22c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ) (c : K)
    (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  classical
  rw [mem_PolK_iff]
  intro β hβ
  have := support_monomial_subset hβ
  rw [Finset.mem_singleton] at this
  rw [this]; exact h
end Formalism.MainNotions.PlaneGram.TwistData
