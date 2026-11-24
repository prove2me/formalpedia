-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:00:03.685805+00:00
-- url     : https://prove2.me/submissions/0e108f14-8d4e-44b1-ba9b-c5c9f132268b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_prod_factorial_eq

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg α i = d i) :
    vN v (fact α) ≤ vN v (∏ i, (d i).factorial) := by
  rw [vN_prod_factorial_eq hD h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => vN_nonneg hD _)
end Formalism.MainNotions.PlaneGram
