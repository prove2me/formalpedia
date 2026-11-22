-- Prove2me | solution 1 for Comp.fixAux_fixed_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:53.158059+00:00
-- url     : https://prove2.me/submissions/c1b86f3e-2378-4b9f-a770-8de837dc2a08

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_zero
import Theorems.Thm_Comp_fixAux_succ
attribute [local simp] Comp.fixAux_zero

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (hmono : Monotone f) (n : ℕ)
    (x : Finset S) (hx : f x ≤ x) (hcard : x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by
  induction n generalizing x with
  | zero =>
      rw [fixAux_zero]
      have hx0 : x = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hx0
      exact Finset.subset_empty.mp hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact h
      · refine ih (f x) (hmono hx) ?_
        have hss : f x ⊂ x := Finset.ssubset_iff_subset_ne.mpr ⟨hx, h⟩
        have hlt := Finset.card_lt_card hss
        omega
end Comp
