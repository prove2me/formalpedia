-- Prove2me | solution 1 for Erdos835Palomar.johnson_chromaticNumber_composite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:33:48.470562+00:00
-- url     : https://prove2.me/submissions/67c4d655-0655-4ca9-abcd-7760c044d536

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
public import Theorems.Thm_Erdos835Palomar_not_property_of_not_prime
public import Theorems.Thm_Erdos835Palomar_le_chromaticNumber
public import Theorems.Thm_Erdos835Palomar_property_iff_chromaticNumber

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution (k : ℕ) (hk : 2 < k) (h : Composite (k + 1)) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  refine lt_of_le_of_ne (le_chromaticNumber (by omega)) fun heq => ?_
  exact not_property_of_not_prime k (by omega) h.2
    ((property_iff_chromaticNumber k (by omega)).mp heq.symm)
end Erdos835Palomar
