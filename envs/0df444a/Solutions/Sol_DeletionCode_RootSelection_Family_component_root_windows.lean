-- Prove2me | solution 1 for DeletionCode.RootSelection.Family.component_root_windows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:55.680854+00:00
-- url     : https://prove2.me/submissions/7a97fab1-b508-42c3-abc4-b0943c13d7ff

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection
import Theorems.Thm_DeletionCode_RootSelection_Family_supplier_adjacent
import Theorems.Thm_DeletionCode_RootSelection_Family_exists_minimal_in_component

set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family
namespace DeletionCode.RootSelection.Family
theorem _root_.solution {B : Type*} (F : Family B)
    (x : Letters) (n L : ℕ) (hgen : F.Generating x n L) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ i, i ≤ F.extra r false → WordPaths.Occurs x n (F.path r false) i L := by
  obtain ⟨r, hr, hmin⟩ := F.exists_minimal_in_component L b
  refine ⟨r, hr, ?_⟩
  intro i hi
  rcases hgen r i hi with hx | ⟨a, side, j, hearlier, hj, hgram⟩
  · exact hx
  · have hadj : F.Adjacent L r a := F.supplier_adjacent L r a side i j hi hj hgram
    have haconn : F.Connected L a b :=
      Relation.EqvGen.trans a r b
        (Relation.EqvGen.symm r a (Relation.EqvGen.rel r a hadj)) hr
    have hle := hmin a haconn
    omega
end DeletionCode.RootSelection.Family
