-- Prove2me | solution 1 for DeletionCode.SignedSupport.rule_negative_of_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:16.182961+00:00
-- url     : https://prove2.me/submissions/b91de847-406f-4fbb-93cb-4ce3c068f62b

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_bubble_negative_value
import Theorems.Thm_DeletionCode_SignedSupport_rule_value_at_gram

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L)
    (hg : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    ruleSpectrum F L S g = -1 := by
  rw [rule_value_at_gram F L H S hdis b hb g ⟨false, hg⟩]
  exact bubble_negative_value F L H b g hg
end DeletionCode.SignedSupport
