-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_prod_factorial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:40.177165+00:00
-- url     : https://prove2.me/submissions/d894282e-4d8a-41be-8f25-ae891c3c0220

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_prod_factorial_eq

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
    vN v (∏ i, (d i).factorial) =
      vN v (fact α) + ∑ i : L, vN v (Nat.multinomial univ fun a : Fin r => α (i, a)) := by
  rw [prod_factorial_eq h,
    vN_mul hD (fact_ne_zero α) (Finset.prod_ne_zero_iff.mpr fun i _ => (Nat.multinomial_pos _ _).ne'),
    vN_prod hD _ _ (fun i _ => (Nat.multinomial_pos _ _).ne')]
end Formalism.MainNotions.PlaneGram
