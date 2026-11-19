-- Prove2me | solution 1 for DeletionCode.SeedLookup.recoverWindow_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:21.875716+00:00
-- url     : https://prove2.me/submissions/cee62b03-7ce1-49f6-806a-c9d65e74ec92

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
import Theorems.Thm_DeletionCode_SeedLookup_lookup_sound

set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution (x : Letters) (n k L r : ℕ) (seed : Fin k → Bool)
    (bits : Fin L → Bool) (h : recoverWindow x n k L r seed = some bits) :
    ∃ a, Matches x n k L r seed a ∧ bits = fun i => x (a + i.val) := by
  unfold recoverWindow at h
  cases heq : lookup x n k L r seed with
  | none => simp [heq] at h
  | some a =>
    simp only [heq, Option.map_some, Option.some.injEq] at h
    exact ⟨a, lookup_sound x n k L r a seed heq, h.symm⟩
end DeletionCode.SeedLookup
