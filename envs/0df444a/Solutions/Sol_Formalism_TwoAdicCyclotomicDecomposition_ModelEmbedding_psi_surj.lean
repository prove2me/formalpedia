-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.psi_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:14.407493+00:00
-- url     : https://prove2.me/submissions/594afdc4-01c9-4f7f-9d58-b969eb0a9754

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mod_four_character_five
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mod_eight_character_five

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
theorem _root_.solution (k : ℕ) : Function.Surjective (psi k) := by
  rintro ⟨a, b, c⟩
  rcases Int.units_eq_one_or b with rfl | rfl
  · refine ⟨(1, a, a * c), ?_⟩
    simp [psi, ← mul_assoc, Int.units_mul_self]
  · refine ⟨(u5 (k + 3), a, a * c), ?_⟩
    simp [psi, mod_four_character_five, mod_eight_character_five, ← mul_assoc, Int.units_mul_self]
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
