-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lsup_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:58.790826+00:00
-- url     : https://prove2.me/submissions/f13b1252-fb75-4663-9ef3-3b7324555e93

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_monomial

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
theorem _root_.solution {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (F : MvPolynomial σ K) :
    lsup φ F = ∑ α ∈ F.support, F.coeff α • φ α := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => lsup_monomial φ α _
end Formalism.MainNotions.PlaneGram
