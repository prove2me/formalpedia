-- Prove2me | solution 1 for DeletionCode.RootSelection.Family.exists_minimal_in_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:59:20.464422+00:00
-- url     : https://prove2.me/submissions/5857fe0c-6558-4785-9a42-07343edc8f92

import Definitions.Def_DeletionCode_WordPaths
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Definitions.Def_DeletionCode_RootSelection

set_option autoImplicit true
open DeletionCode DeletionCode.RootSelection
open Windows
open DeletionCode.RootSelection.Family
namespace DeletionCode.RootSelection.Family
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ a, F.Connected L a b → F.rank r ≤ F.rank a := by
  classical
  let P : ℕ → Prop := fun k => ∃ a, F.Connected L a b ∧ F.rank a = k
  have hex : ∃ k, P k := ⟨F.rank b, b, Relation.EqvGen.refl b, rfl⟩
  obtain ⟨r, hr, hrank⟩ := Nat.find_spec hex
  refine ⟨r, hr, ?_⟩
  intro a ha
  have hle : Nat.find hex ≤ F.rank a := Nat.find_min' hex ⟨a, ha, rfl⟩
  omega
end DeletionCode.RootSelection.Family
