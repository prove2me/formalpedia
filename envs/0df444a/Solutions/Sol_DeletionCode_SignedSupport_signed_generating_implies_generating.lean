-- Prove2me | solution 1 for DeletionCode.SignedSupport.signed_generating_implies_generating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:50.621596+00:00
-- url     : https://prove2.me/submissions/3633413d-f3cf-4b3d-b951-73d802f020ce

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_iff_agree
import Theorems.Thm_DeletionCode_SignedSupport_rule_negative_of_window
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_wordSpectrum_nonzero_occurs

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} [Fintype B]
    (F : Family B) (x : Letters) (n L : ℕ)
    (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (hgen : SignedGenerating F x n L) : F.Generating x n L := by
  intro b i hi
  let g : Gram L := gram (F.path b false) L i
  have hb : b ∈ ruleBubbles F (F.rank b) := by simp [ruleBubbles]
  have hneg : g ∈ windowSet (F.path b false) L (F.extra b false) :=
    ⟨⟨i, by omega⟩, rfl⟩
  have hvalue := rule_negative_of_window F L H (ruleBubbles F (F.rank b))
    (hdis (F.rank b)) b hb g hneg
  rcases hgen (F.rank b) g hvalue with hbase | ⟨j, hj, hsupplier⟩
  · obtain ⟨a, ha, hagree⟩ := wordSpectrum_nonzero_occurs x n L g hbase
    exact Or.inl ⟨a, ha, (gram_eq_iff_agree x (F.path b false) L a i).mp hagree⟩
  · obtain ⟨a, ha, side, offset, hgram⟩ :=
      (rule_support_iff F L H (ruleBubbles F j) (hdis j) g).mp hsupplier
    have hrank : F.rank a = j := (Finset.mem_filter.mp ha).2
    have hoffset := offset.isLt
    refine Or.inr ⟨a, side, offset.val, by omega, by omega, ?_⟩
    exact (gram_eq_iff_agree (F.path b false) (F.path a side) L i offset.val).mp
      hgram.symm
end DeletionCode.SignedSupport
