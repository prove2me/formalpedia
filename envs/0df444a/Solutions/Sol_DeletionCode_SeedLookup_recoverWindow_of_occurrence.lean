-- Prove2me | solution 1 for DeletionCode.SeedLookup.recoverWindow_of_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:08.855573+00:00
-- url     : https://prove2.me/submissions/939c7173-3ff1-49d8-97fb-95950572df97

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_SeedLookup
import Theorems.Thm_DeletionCode_SeedLookup_lookup_eq_some_iff

set_option autoImplicit true
open DeletionCode DeletionCode.SeedLookup
open Windows
namespace DeletionCode.SeedLookup
theorem _root_.solution
    (x target : Letters) (n k L r a w : ℕ) (seed : Fin k → Bool)
    (hx : KUnique x n k) (hr : r + k ≤ L) (ha : a + L ≤ n)
    (hocc : Agree x a target w L)
    (hseed : ∀ i : Fin k, seed i = target (w + r + i.val)) :
    recoverWindow x n k L r seed = some (fun i : Fin L => target (w + i.val)) := by
  have hmatch : Matches x n k L r seed a := by
    refine ⟨hr, ha, ?_⟩
    intro i
    have hi : r + i.val < L := by omega
    calc
      x (a + r + i.val) = target (w + r + i.val) := by
        simpa [Nat.add_assoc] using hocc (r + i.val) hi
      _ = seed i := (hseed i).symm
  have hlookup := (lookup_eq_some_iff x n k L r a seed hx).mpr hmatch
  unfold recoverWindow
  rw [hlookup]
  simp only [Option.map_some, Option.some.injEq]
  funext i
  exact hocc i.val i.isLt
end DeletionCode.SeedLookup
