-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.appMon_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:39.413702+00:00
-- url     : https://prove2.me/submissions/50238b1e-29ea-4566-9549-c85cdb406fab

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_putL_monomial
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
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
variable {I : Type} [Fintype I]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) :
    appMon i P cls cf ρ' δ κ α = putL i α (∑ s, if cls s = (fun a => letE α i a % P) then
      monomial (ρ' s + P • (δ s + (divE P (letE α i) - κ s))) (cf s * bin (κ s) (divE P (letE α i)))
      else 0) := by
  rw [map_sum, appMon]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : cls s = (fun a => α (i, a) % P)
  · rw [if_pos h, if_pos (show cls s = fun a => letE α i a % P from h), putL_monomial]
  · rw [if_neg h, if_neg (show ¬ cls s = fun a => letE α i a % P from h), map_zero]
end Formalism.MainNotions.PlaneGram
