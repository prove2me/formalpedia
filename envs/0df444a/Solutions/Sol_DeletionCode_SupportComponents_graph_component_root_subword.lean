-- Prove2me | solution 1 for DeletionCode.SupportComponents.graph_component_root_subword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:21.105888+00:00
-- url     : https://prove2.me/submissions/4af72f40-551e-4292-9b4e-76376aef81ca

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents
import Theorems.Thm_DeletionCode_RootSelection_Family_component_root_subword


set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection
namespace DeletionCode.SupportComponents
theorem _root_.solution {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (hgen : F.Generating x n L) (v : SupportedVertex F L) :
    ∃ r a, GraphConnected F L v.val (representative F L r) ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  obtain ⟨r, a, hr, ha, hagree⟩ := F.component_root_subword x n k L hx hk hgen b
  have hroot := (connected_iff_graph_connected F L (by omega) hstart r b).mp hr
  have hvb : GraphConnected F L v.val (representative F L b) := by
    rw [hv]
    exact Relation.EqvGen.symm _ _ (representative_connected F L hstart b side i hi)
  exact ⟨r, a, Relation.EqvGen.trans _ _ _ hvb (Relation.EqvGen.symm _ _ hroot),
    ha, hagree⟩
end DeletionCode.SupportComponents
