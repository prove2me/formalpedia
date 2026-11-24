-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_JJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:49:06.539135+00:00
-- url     : https://prove2.me/submissions/88ba48d5-fac3-41e9-a968-b3857f399c56

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_JJ_ne_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_JJ_mul_self

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
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (n : ℕ) : orderOf (JJ n) = 2 := orderOf_eq_prime (by rw [sq]; exact JJ_mul_self n) (JJ_ne_one n)
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
