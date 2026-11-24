-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.monomial_mem_PolK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:29.645719+00:00
-- url     : https://prove2.me/submissions/3433aa4f-cb98-428a-b24b-3106faa32130

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} {r : ℕ} (ζ : L × Fin r →₀ ℕ) (c : K) :
    monomial ζ c ∈ PolK K r (fun i => ldeg ζ i) := by
  rw [PolK, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' := MvPolynomial.support_monomial_subset (Finset.mem_coe.1 hm)
  rw [Finset.mem_singleton] at hm'
  subst hm'
  intro i
  rfl
end Formalism.MainNotions.PlaneGram
