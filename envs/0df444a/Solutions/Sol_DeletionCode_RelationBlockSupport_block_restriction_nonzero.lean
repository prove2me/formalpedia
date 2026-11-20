-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.block_restriction_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:42.001127+00:00
-- url     : https://prove2.me/submissions/1e6d8227-d137-4c61-b477-07bdac608451

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
import Theorems.Thm_DeletionCode_RelationBlockSupport_partial_sum_nonzero
import Theorems.Thm_DeletionCode_RelationBlockSupport_restriction_eq_at
import Theorems.Thm_DeletionCode_RelationBlockSupport_partial_support
import Theorems.Thm_DeletionCode_RelationBlockSupport_outside_block_vanishes

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (T : Finset I)
    (hactive : ∃ i ∈ T, a i ≠ 0)
    (hclosed : BlockClosed G (↑T : Set I)) :
    ∃ g, w g ≠ 0 ∧ ∃ i ∈ T, G i g ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := partial_sum_nonzero (fun i g => (G i g : ℚ)) hG T a hactive
  have hs := partial_support G T a g hg
  have heq := restriction_eq_at G w a hrel T g
    (outside_block_vanishes G T hclosed g hs)
  refine ⟨g, ?_, hs⟩
  intro hw
  apply hg
  simpa only [hw, Int.cast_zero] using heq.symm
end DeletionCode.RelationBlockSupport
