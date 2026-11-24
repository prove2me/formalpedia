-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_monomial_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:07:39.492627+00:00
-- url     : https://prove2.me/submissions/2f206144-7aaf-45de-b389-983b53435fd6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial


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
theorem _root_.solution {σ : Type} (g : (σ →₀ ℕ) → K) (μ : σ →₀ ℕ) (Q : MvPolynomial σ K) :
    dg g (monomial μ 1 * Q) = monomial μ 1 * dg (fun β => g (μ + β)) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial β c => rw [monomial_mul, dg_monomial, dg_monomial, monomial_mul, one_mul, one_mul]
  | add p q hp hq => rw [mul_add, map_add, map_add, mul_add, hp, hq]
end Formalism.MainNotions.PlaneGram
