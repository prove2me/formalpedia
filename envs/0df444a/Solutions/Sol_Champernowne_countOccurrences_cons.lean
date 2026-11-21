-- Prove2me | solution 1 for Champernowne.countOccurrences_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:01.934812+00:00
-- url     : https://prove2.me/submissions/bd1f4c0e-d002-4f9c-9e85-d7d9640997f2

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w l : List ℕ) (x : ℕ) :
    countOccurrences w (x :: l)
      = countOccurrences w l + (if w.isPrefixOf (x :: l) then 1 else 0) := by
  simp [countOccurrences, List.countP_cons]
end Champernowne
