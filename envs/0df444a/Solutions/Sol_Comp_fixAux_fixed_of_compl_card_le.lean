-- Prove2me | solution 1 for Comp.fixAux_fixed_of_compl_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:28:12.943366+00:00
-- url     : https://prove2.me/submissions/cb629dbc-80be-4f47-8e8a-3a1bbad76eba

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
    (x : Finset S) (hx : x ≤ f x) (hcard : Fintype.card S - x.card ≤ n) :
    f (fixAux f n x) = fixAux f n x := by
  induction n generalizing x with
  | zero =>
      rw [fixAux_zero]
      have hle : x.card ≤ Fintype.card S := by
        simpa only [Finset.card_univ] using Finset.card_le_univ x
      have hxu : x = Finset.univ := Finset.eq_univ_of_card x (by omega)
      subst hxu
      exact le_antisymm (Finset.subset_univ _) hx
  | succ n ih =>
      rw [fixAux_succ]
      split_ifs with h
      · exact h
      · refine ih (f x) (hmono hx) ?_
        have hss : x ⊂ f x := Finset.ssubset_iff_subset_ne.mpr ⟨hx, fun he => h he.symm⟩
        have hlt := Finset.card_lt_card hss
        have hle : (f x).card ≤ Fintype.card S := by
          simpa only [Finset.card_univ] using Finset.card_le_univ (f x)
        omega
end Comp
