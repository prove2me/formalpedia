-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.ddiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:48.38024+00:00
-- url     : https://prove2.me/submissions/d25b152b-033c-4e87-8a6e-50e65317ff50

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : ddiv M F = ddivL M F := by
  rw [ddivL, lsup_apply, ddiv]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [smul_monomial, smul_eq_mul]
  · rw [smul_zero]
end Formalism.MainNotions.PlaneGram
