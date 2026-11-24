-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.psi_JJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:07.373587+00:00
-- url     : https://prove2.me/submissions/1d5ad50c-b7e8-4643-b153-5cafc021f83c

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mod_four_character_neg_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_mod_eight_character_neg_one

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
theorem _root_.solution (k : ℕ) : psi k (JJ (k + 3)) = 1 := by
  simp [psi, JJ, mod_four_character_neg_one, mod_eight_character_neg_one]
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
