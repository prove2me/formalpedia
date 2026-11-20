-- Prove2me | solution 1 for DeletionCode.SignedSupport.signed_graph_connected_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:21.667276+00:00
-- url     : https://prove2.me/submissions/60abaeb3-33c3-443b-9eeb-17cceebd1ba7

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_signed_support_edge_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    SignedGraphConnected F L u v ↔ SupportComponents.GraphConnected F L u v := by
  have heq : signedSupportEdge F L = SupportComponents.Edge F L := by
    funext a b
    exact propext (signed_support_edge_iff F L H hdis a b)
  unfold SignedGraphConnected SupportComponents.GraphConnected
  rw [heq]
end DeletionCode.SignedSupport
