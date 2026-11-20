-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.partial_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:56.105981+00:00
-- url     : https://prove2.me/submissions/f35eeec0-a5a6-47ba-82c3-11bbe57c5129

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} {L : ℕ}
    (G : I → Gram L → ℤ) (T : Finset I) (a : I → ℚ) (g : Gram L)
    (hne : (∑ i ∈ T, a i * (G i g : ℚ)) ≠ 0) :
    ∃ i ∈ T, G i g ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  apply hne
  apply Finset.sum_eq_zero
  intro i hi
  simp [hnone i hi]
end DeletionCode.RelationBlockSupport
