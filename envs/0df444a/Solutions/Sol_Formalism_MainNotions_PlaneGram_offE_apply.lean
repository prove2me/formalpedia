-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.offE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:32.300045+00:00
-- url     : https://prove2.me/submissions/514a03c6-854d-4556-bfa4-15661ddb0813

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (α : L × Fin r →₀ ℕ) (j : L) (a : Fin r) :
    offE i α (j, a) = if j = i then 0 else α (j, a) := by
  unfold offE
  rw [Finsupp.filter_apply]
  by_cases h : j = i <;> simp [h]
end Formalism.MainNotions.PlaneGram
