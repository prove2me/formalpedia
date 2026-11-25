-- Prove2me | solution 1 for Erdos835Palomar.property_iff_chromaticNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:22:35.529348+00:00
-- url     : https://prove2.me/submissions/a711059e-2568-402c-8a8a-5c9ee88bdddf

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_property_of_coloring
public import Theorems.Thm_Erdos835Palomar_colorable_of_property
public import Theorems.Thm_Erdos835Palomar_le_chromaticNumber

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔ Property k := by
  constructor
  · intro h
    have hcol : J(2 * k, k).Colorable (k + 1) := by
      rw [← chromaticNumber_le_iff_colorable, h]; push_cast; exact le_rfl
    exact property_of_coloring (hcol.toColoring (by simp))
  · intro hP
    apply le_antisymm
    · have := (colorable_of_property hP).chromaticNumber_le
      push_cast at this; exact this
    · exact le_chromaticNumber hk
end Erdos835Palomar
