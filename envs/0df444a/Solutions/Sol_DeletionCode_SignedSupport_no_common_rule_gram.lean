-- Prove2me | solution 1 for DeletionCode.SignedSupport.no_common_rule_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:50.681693+00:00
-- url     : https://prove2.me/submissions/9197b8f8-38bd-42a9-99ec-3c2d00a29a50

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_source_vertices

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ) (S : Finset B)
    (hdis : VertexDisjointOn F L S) (a b : B) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (g : Gram L) (hga : HasGram F L a g) (hgb : HasGram F L b g) :
    False := by
  obtain ⟨sa, i, hi⟩ := hga
  obtain ⟨sb, j, hj⟩ := hgb
  have hiBound := i.isLt
  have hjBound := j.isLt
  exact hdis a ha b hb hab sa sb i.val j.val (by omega) (by omega)
    (gram_eq_source_vertices F L a b sa sb i.val j.val (hi.trans hj.symm))
end DeletionCode.SignedSupport
