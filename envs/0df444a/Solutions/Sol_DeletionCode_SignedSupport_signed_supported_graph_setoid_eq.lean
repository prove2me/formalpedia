-- Prove2me | solution 1 for DeletionCode.SignedSupport.signed_supported_graph_setoid_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:51.814722+00:00
-- url     : https://prove2.me/submissions/f07e83e7-802b-47aa-af62-d85d5da6d557

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
import Theorems.Thm_DeletionCode_SignedSupport_signed_graph_connected_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i)) :
    signedSupportedGraphSetoid F L = SupportComponents.supportedGraphSetoid F L := by
  apply Setoid.ext
  intro u v
  exact signed_graph_connected_iff F L H hdis u.val v.val
end DeletionCode.SignedSupport
