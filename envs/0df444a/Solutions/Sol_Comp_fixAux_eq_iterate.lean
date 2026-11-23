-- Prove2me | solution 1 for Comp.fixAux_eq_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:56.429104+00:00
-- url     : https://prove2.me/submissions/884037b7-e0a8-4e81-86eb-866ac4d585cb

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_zero
import Theorems.Thm_Comp_fixAux_succ
attribute [local simp] Comp.fixAux_zero

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (n : ℕ) (x : Finset S) :
    fixAux f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rw [fixAux_zero, Function.iterate_zero_apply]
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · have hfix : ∀ k, f^[k] x = x := by
          intro k
          induction k with
          | zero => rw [Function.iterate_zero_apply]
          | succ k ihk => rw [Function.iterate_succ_apply', ihk, h]
        rw [hfix (n + 1)]
      · rw [ih (f x), Function.iterate_succ_apply]
end Comp
