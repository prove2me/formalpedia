-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:03:12.853811+00:00
-- url     : https://prove2.me/submissions/0b9eb5e7-05c0-4989-af7f-eb5925abdb3f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_natLog_le_term
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_multinomial_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
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
    vN v (∏ i, (d i).factorial) - kapL p r d ≤ vN v (fact α) := by
  rw [vN_prod_factorial_eq hD h]
  have hs : ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) ≤ kapL p r d := by
    unfold kapL
    apply Finset.sum_le_sum
    intro i _
    have e : ∑ a : Fin r, α (i, a) = d i := h i
    have := vN_multinomial_le hD (fun a : Fin r => α (i, a))
    rw [e] at this
    exact this.trans (natLog_le_term (two_le_p hD) r (d i))
  linarith
end Formalism.MainNotions.PlaneGram
