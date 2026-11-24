-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vN_multinomial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:21.431989+00:00
-- url     : https://prove2.me/submissions/7abdfcca-9d6e-4201-aba1-d4e4817cefc0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_multinomial_fact_le

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
theorem _root_.solution (hD : DVRHyp v p) {r : ℕ} (f : Fin r → ℕ) :
    vN v (Nat.multinomial univ f) ≤ (r : ℝ) * (Nat.log p (∑ a, f a) : ℝ) := by
  rw [vN_eq hD, ← Nat.factorization_def _ hD.prime]
  have := multinomial_fact_le p f Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this
end Formalism.MainNotions.PlaneGram
