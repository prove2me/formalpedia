-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.mem_zpowers_JJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:04:04.335369+00:00
-- url     : https://prove2.me/submissions/bd974e89-beeb-4a1c-9029-763846ff2fbc

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
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
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution {n : ℕ} {g : GalL n} (h : g ∈ zpowers (JJ n)) : g = 1 ∨ g = JJ n := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
  rw [← zpow_mod_orderOf, orderOf_JJ]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; simp [hk]
  · right; simp [hk]
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
