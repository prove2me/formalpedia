-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.gamEModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:12.136881+00:00
-- url     : https://prove2.me/submissions/6164d29e-9dfd-4c9a-85a5-170fc6ebcc86

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_card_GamE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : GamEModel := by
  unfold GamEModel
  intro s
  refine ⟨card_GamE s, ⟨eGamE s⟩, ?_, ?_⟩
  · unfold JJ
    rw [QuotientGroup.eq, mem_zpowers_sq gen_sq]
    right
    simp
  · apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow]
      have hJ : JJ (s + 2) ^ 2 = 1 := by
        unfold JJ
        rw [Prod.pow_mk, Prod.pow_mk, neg_one_sq, neg_one_sq]
        all_goals rfl
      rw [hJ, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff, mem_zpowers_sq gen_sq]
      unfold JJ
      rintro (h1 | h1) <;>
      · have h2 : (-1 : ℤˣ) = 1 := congrArg (fun x : GalL (s + 2) => x.2.1) h1
        exact absurd h2 (by decide)
end Formalism.TwoAdicCyclotomicDecomposition
