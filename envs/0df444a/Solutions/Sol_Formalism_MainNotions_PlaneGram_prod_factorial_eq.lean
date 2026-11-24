-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.prod_factorial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:22.49027+00:00
-- url     : https://prove2.me/submissions/1cac5606-4b86-42e2-9a7c-fe2df4b46f8b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_eq_prod_letters

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
theorem _root_.solution {L : Type} [Fintype L] {r : ℕ} {α : L × Fin r →₀ ℕ} {d : L → ℕ}
    (h : ∀ i, ldeg α i = d i) :
    ∏ i, (d i).factorial = fact α * ∏ i : L, Nat.multinomial univ fun a : Fin r => α (i, a) := by
  rw [fact_eq_prod_letters, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← h i]
  simp only [ldeg]
  exact (Nat.multinomial_spec _ _).symm
end Formalism.MainNotions.PlaneGram
