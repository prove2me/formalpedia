-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_length_marker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:17.818208+00:00
-- url     : https://prove2.me/submissions/cc534110-b25c-4870-9cf3-d029c9d371f0

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_grows

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
theorem _root_.solution {t : ℕ} {l : Fin k} (hl : l ∈ active W t) :
    t ≤ (marker W t l).length := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have := ih (active_succ_subset W t hl)
    have := marker_grows hl
    omega
end DeciSigma1.Holes.Fresh
