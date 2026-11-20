-- Prove2me | solution 1 for DeletionCode.SignedSupport.rule_value_at_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:47.946046+00:00
-- url     : https://prove2.me/submissions/3b1bf75c-19c5-48a6-ba0a-9b5c73716257

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_bubble_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_no_common_rule_gram

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L) (hg : HasGram F L b g) :
    ruleSpectrum F L S g = bubbleSpectrum F L b g := by
  classical
  unfold ruleSpectrum
  apply Finset.sum_eq_single b
  · intro a ha hab
    by_contra hnonzero
    exact no_common_rule_gram F L S hdis a b ha hb hab g
      ((bubble_support_iff F L H a g).mp hnonzero) hg
  · intro hnot
    exact False.elim (hnot hb)
end DeletionCode.SignedSupport
