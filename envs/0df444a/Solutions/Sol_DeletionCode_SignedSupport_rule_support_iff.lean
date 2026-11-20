-- Prove2me | solution 1 for DeletionCode.SignedSupport.rule_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:12.344176+00:00
-- url     : https://prove2.me/submissions/72abbeb3-3937-4670-a6fb-5cb846867473

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_bubble_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_rule_value_at_gram

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (g : Gram L) :
    ruleSpectrum F L S g ≠ 0 ↔ ∃ b ∈ S, HasGram F L b g := by
  classical
  constructor
  · intro h
    by_contra hnone
    apply h
    unfold ruleSpectrum
    apply Finset.sum_eq_zero
    intro b hb
    by_contra hnonzero
    exact hnone ⟨b, hb, (bubble_support_iff F L H b g).mp hnonzero⟩
  · rintro ⟨b, hb, hg⟩
    rw [rule_value_at_gram F L H S hdis b hb g hg]
    exact (bubble_support_iff F L H b g).mpr hg
end DeletionCode.SignedSupport
