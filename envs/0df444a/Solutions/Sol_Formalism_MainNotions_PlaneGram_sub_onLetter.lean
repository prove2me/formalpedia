-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.sub_onLetter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:41.406394+00:00
-- url     : https://prove2.me/submissions/7b0cce9e-48ff-4cfd-addd-4d5b08fb1941

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_onLetter_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_offE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (M : Fin r →₀ ℕ) (α : L × Fin r →₀ ℕ) :
    α - onLetter i M = offE i α + onLetter i (letE α i - M) := by
  ext ⟨j, a⟩
  simp only [Finsupp.tsub_apply, Finsupp.add_apply, offE_apply, onLetter_apply, letE_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]
end Formalism.MainNotions.PlaneGram
