-- Prove2me | solution 1 for DeletionCode.WalkSelection.coordinate_unchanged_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:00.236882+00:00
-- url     : https://prove2.me/submissions/25dbe3f5-1565-4c9b-8b93-ca20785f2560

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (n : ℕ) (hn : n ≤ m) (h : H)
    (hzero : ∀ j : Fin m, j.val < n → walkStep p j h = 0) :
    p ⟨n, by omega⟩ h = p 0 h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (by omega) (fun j hj => hzero j (by omega))
    let j : Fin m := ⟨n, by omega⟩
    have hstep := hzero j (by dsimp [j]; omega)
    change p ⟨n + 1, by omega⟩ h - p ⟨n, by omega⟩ h = 0 at hstep
    exact (sub_eq_zero.mp hstep).trans hprev
end DeletionCode.WalkSelection
