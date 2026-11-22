-- Prove2me | solution 1 for Comp.gfp_le_coe_fixAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:19.317174+00:00
-- url     : https://prove2.me/submissions/07038fc4-dda8-45d9-85d7-41a78a81170f

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_zero
import Theorems.Thm_Comp_fixAux_succ
import Theorems.Thm_OrderHom_gfp_le_of_step

attribute [local simp] Comp.fixAux_zero

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) (n : ℕ) (x : Finset S)
    (hx : F.gfp ≤ (↑x : Set S)) :
    F.gfp ≤ (↑(fixAux f n x) : Set S) := by
  induction n generalizing x hx with
  | zero =>
      rw [fixAux_zero]
      exact hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact hx
      · exact ih (f x) (OrderHom.gfp_le_of_step F hx (hf x))
end Comp
