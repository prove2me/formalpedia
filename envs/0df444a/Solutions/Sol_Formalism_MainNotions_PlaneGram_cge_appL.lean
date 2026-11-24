-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_appL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:41:00.504912+00:00
-- url     : https://prove2.me/submissions/2e357a23-0225-4390-9827-87ab1b291d4a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_appMon
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_smul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply


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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (v : AddValuation K (WithTop ℚ)) (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K)
    (ρ' δ κ : I → (Fin r →₀ ℕ)) (hcf : ∀ s, 0 ≤ v (cf s)) {a : ℝ} {G : MvPolynomial (L × Fin r) K}
    (hG : cge v a G) : cge v a (appL i P cls cf ρ' δ κ G) := by
  rw [appL, lsup_apply]
  apply cge_sum v
  intro α _
  have h := cge_smul v (hG α) (cge_appMon v i P cls cf ρ' δ κ hcf α)
  rwa [add_zero] at h
end Formalism.MainNotions.PlaneGram
