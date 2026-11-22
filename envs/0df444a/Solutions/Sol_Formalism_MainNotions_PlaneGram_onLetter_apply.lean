-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.onLetter_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:16.601879+00:00
-- url     : https://prove2.me/submissions/150d382c-f763-4823-89e4-109407fee058

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial

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
variable {L : Type} [DecidableEq L] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (β : Fin r →₀ ℕ) (j : L) (a : Fin r) :
    onLetter i β (j, a) = if j = i then β a else 0 := by
  unfold onLetter
  by_cases h : j = i
  · subst h
    rw [if_pos rfl]
    exact Finsupp.mapDomain_apply (fun x y hxy => by simpa using hxy) β a
  · rw [if_neg h]
    have hne : (j, a) ∉ Set.range (fun b : Fin r => (i, b)) := by
      rintro ⟨b, hb⟩
      exact h (congrArg Prod.fst hb).symm
    first
      | exact Finsupp.mapDomain_of_notMem_range _ _ hne
      | exact Finsupp.mapDomain_notin_range _ _ hne
end Formalism.MainNotions.PlaneGram
