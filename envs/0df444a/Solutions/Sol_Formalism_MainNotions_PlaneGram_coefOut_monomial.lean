-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coefOut_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:27.940927+00:00
-- url     : https://prove2.me/submissions/96be5b70-d9db-4fa5-a073-9ef8c2a74179

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (μ α : L × Fin r →₀ ℕ) (c : K) :
    coefOut out μ (monomial α c) = if eOut out α = μ then monomial (eIn out α) c else 0 := by
  rw [coefOut_eq_sum out μ (monomial α c) {α} support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]
end Formalism.MainNotions.PlaneGram
