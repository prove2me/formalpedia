-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.kapL_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:20.352808+00:00
-- url     : https://prove2.me/submissions/09847daf-83a0-40db-9650-46dc03f02613

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_logb_add_mono
import Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_term_nonneg

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (r : ℕ) {L : Type} [Fintype L] {d d' : L → ℕ}
    (h : ∀ i, d i ≤ d' i) : kapL p r d ≤ kapL p r d' := by
  unfold kapL
  apply Finset.sum_le_sum
  intro i _
  by_cases h0 : d i = 0
  · rw [if_pos h0]
    exact kapL_term_nonneg hp r (d' i)
  · have h1 : d' i ≠ 0 := by
      have := h i
      omega
    rw [if_neg h0, if_neg h1]
    exact mul_le_mul_of_nonneg_left (logb_add_mono hp r (by omega) (h i)) (Nat.cast_nonneg r)
end Formalism.MainNotions.PlaneGram
