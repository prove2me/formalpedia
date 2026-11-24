-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.index_ker_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:04.582643+00:00
-- url     : https://prove2.me/submissions/170c8b80-61ad-4315-a658-0fde0697ad5d

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_card_units_int
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ModelEmbedding_psi_surj

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
theorem _root_.solution (k : ℕ) : (psi k).ker.index = 8 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (psi_surj k), Subgroup.card_top,
    Nat.card_prod, Nat.card_prod, card_units_int]
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
