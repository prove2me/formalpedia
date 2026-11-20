-- Prove2me | solution 1 for DeletionCode.SupportComponents.bubble_vertices_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:20.222229+00:00
-- url     : https://prove2.me/submissions/724aedfd-51f3-4e6c-adfa-5436824fa576

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents

set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection
namespace DeletionCode.SupportComponents
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (u v : Vertex L) (hu : HasVertex F L b u) (hv : HasVertex F L b v) :
    GraphConnected F L u v := by
  obtain ⟨su, i, hi, rfl⟩ := hu
  obtain ⟨sv, j, hj, rfl⟩ := hv
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (representative_connected F L hstart b su i hi))
    (representative_connected F L hstart b sv j hj)
end DeletionCode.SupportComponents
