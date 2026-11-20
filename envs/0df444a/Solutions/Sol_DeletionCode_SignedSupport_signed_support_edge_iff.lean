-- Prove2me | solution 1 for DeletionCode.SignedSupport.signed_support_edge_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:47.929926+00:00
-- url     : https://prove2.me/submissions/5b10d18c-d587-4c9f-a8ba-e6be547a2189

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_prefix_gram
import Theorems.Thm_DeletionCode_SignedSupport_suffix_gram

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    signedSupportEdge F L u v ↔ SupportComponents.Edge F L u v := by
  constructor
  · rintro ⟨rank, g, hg, hu, hv⟩
    obtain ⟨b, hb, side, i, hi⟩ :=
      (rule_support_iff F L H (ruleBubbles F rank) (hdis rank) g).mp hg
    have hbound := i.isLt
    refine ⟨b, side, i.val, by omega, ?_, ?_⟩
    · rw [← hi] at hu
      simpa only [prefix_gram] using hu
    · rw [← hi] at hv
      simpa only [suffix_gram] using hv
  · rintro ⟨b, side, i, hi, hu, hv⟩
    let g := gram (F.path b side) L i
    have hb : b ∈ ruleBubbles F (F.rank b) := by simp [ruleBubbles]
    have hg : HasGram F L b g := ⟨side, ⟨i, by omega⟩, rfl⟩
    refine ⟨F.rank b, g,
      (rule_support_iff F L H (ruleBubbles F (F.rank b)) (hdis (F.rank b)) g).mpr
        ⟨b, hb, hg⟩, ?_, ?_⟩
    · exact hu.trans (prefix_gram F L b side i).symm
    · exact hv.trans (suffix_gram F L b side i).symm
end DeletionCode.SignedSupport
