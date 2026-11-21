-- Prove2me | solution 1 for Champernowne.countOccurrences_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:40.224267+00:00
-- url     : https://prove2.me/submissions/0e3207b9-be8f-48ed-b497-958539beb437

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
theorem _root_.solution {w : List ℕ} (hw : w ≠ []) :
    countOccurrences w [] = 0 := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp [countOccurrences, List.isPrefixOf]
end Champernowne
