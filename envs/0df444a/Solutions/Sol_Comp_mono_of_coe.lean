-- Prove2me | solution 1 for Comp.mono_of_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:09:41.298472+00:00
-- url     : https://prove2.me/submissions/1d4b1599-2e73-4495-9f45-5ba3140f7c50

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
omit [DecidableEq S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) (f : Finset S → Finset S)
    (hf : ∀ x : Finset S, (↑(f x) : Set S) = F ↑x) : Monotone f := by
  intro x y hxy
  have h : (↑(f x) : Set S) ⊆ (↑(f y) : Set S) := by
    rw [hf, hf]
    exact F.monotone (Finset.coe_subset.mpr hxy)
  exact Finset.coe_subset.mp h
end Comp
