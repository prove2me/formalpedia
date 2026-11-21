-- Prove2me | solution 1 for Champernowne.isPrefixOf_append_of_isPrefixOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:36:15.307592+00:00
-- url     : https://prove2.me/submissions/a9fd7c43-62c4-43dd-9113-188b4d28f1d8

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
theorem _root_.solution {w a : List ℕ} (b : List ℕ)
    (h : w.isPrefixOf a) : w.isPrefixOf (a ++ b) := by
  rw [List.isPrefixOf_iff_prefix] at h ⊢
  exact h.trans (List.prefix_append a b)
end Champernowne
