-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_occurrences_eq_of_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:37:45.433251+00:00
-- url     : https://prove2.me/submissions/51a2ffb9-4f47-441e-aa20-e79ff0b8bdac

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_infix_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_eq_of_infix

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
variable {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {m m' : Fin k}
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} {i j : ℕ}
    (h : marker W t m <+: u.drop i) (h' : marker W t m' <+: u.drop j) (hij : i ≤ j)
    (hlen : j + (marker W t m').length ≤ i + (marker W t m).length) :
    i = j ∧ marker W t m' = marker W t m := by
  have heq := marker_eq_of_infix t m' m hm' hm (infix_of_occ h h' hij hlen)
  have : (marker W t m').length = (marker W t m).length := by rw [heq]
  exact ⟨by omega, heq⟩
end DeciSigma1.Holes.Fresh
