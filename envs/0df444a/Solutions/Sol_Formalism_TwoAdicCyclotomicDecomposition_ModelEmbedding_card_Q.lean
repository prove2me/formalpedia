-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.card_Q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:03.766603+00:00
-- url     : https://prove2.me/submissions/4127219d-f5bd-4835-a15c-836ae8785060

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_GalL
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_orderOf_JJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) : Nat.card (GalL n ⧸ zpowers (JJ n)) = 2 ^ n := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (JJ n))
  rw [card_GalL n hn, Nat.card_zpowers, orderOf_JJ, pow_succ] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
