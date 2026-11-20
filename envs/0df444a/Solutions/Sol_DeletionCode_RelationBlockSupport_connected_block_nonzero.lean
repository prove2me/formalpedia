-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.connected_block_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:05.583243+00:00
-- url     : https://prove2.me/submissions/0ee859f6-345f-4ef7-abe2-0415d1fe55a4

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport
import Theorems.Thm_DeletionCode_RelationBlockSupport_block_restriction_nonzero

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I : Type*} [Fintype I] {L : ℕ}
    (G : I → Gram L → ℤ) (w : Gram L → ℤ) (a : I → ℚ)
    (hG : LinearIndependent ℚ (fun i g => (G i g : ℚ)))
    (hrel : RelationSupport.Relation G w a) (b : I)
    (hactive : ∃ i, Connected G b i ∧ a i ≠ 0) :
    ∃ g i, Connected G b i ∧ G i g ≠ 0 ∧ w g ≠ 0 := by
  classical
  let T : Finset I := Finset.univ.filter (fun i => Connected G b i)
  have hmem (i : I) : i ∈ T ↔ Connected G b i := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hT : ∃ i ∈ T, a i ≠ 0 := by
    obtain ⟨i, hi, ha⟩ := hactive
    exact ⟨i, (hmem i).mpr hi, ha⟩
  have hclosed : BlockClosed G (↑T : Set I) := by
    intro i hi j hij
    exact (hmem j).mpr (Relation.EqvGen.trans b i j ((hmem i).mp hi) hij)
  obtain ⟨g, hw, i, hi, hgi⟩ :=
    block_restriction_nonzero G w a hG hrel T hT hclosed
  exact ⟨g, i, (hmem i).mp hi, hgi, hw⟩
end DeletionCode.RelationBlockSupport
