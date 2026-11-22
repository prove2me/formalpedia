-- Prove2me | solution 1 for Comp.coe_fixAux_le_lfp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:37.677213+00:00
-- url     : https://prove2.me/submissions/dd1be8f4-1304-4da6-a489-977f74515794

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_zero
import Theorems.Thm_Comp_fixAux_succ
import Theorems.Thm_OrderHom_le_lfp_of_step

attribute [local simp] Comp.fixAux_zero

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : (↑x : Set S) ≤ F.lfp) :
    (↑(fixAux f n x) : Set S) ≤ F.lfp := by
  induction n generalizing x hx with
  | zero =>
      rw [fixAux_zero]
      exact hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact hx
      · exact ih (f x) (OrderHom.le_lfp_of_step F hx (hf x))
end Comp
