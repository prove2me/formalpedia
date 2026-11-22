-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.marker_eq_of_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:30:51.358401+00:00
-- url     : https://prove2.me/submissions/39038d87-c290-49bd-a4fd-fa272344e5b7

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_FactorAntichain_eq_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_level_anti

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
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} (h : marker W t m <:+ u)
    (h' : marker W t m' <:+ u) : marker W t m = marker W t m' := by
  rcases t with _ | t
  · rfl
  · exact Level.FactorAntichain.eq_of_suffix (level_anti t) hm hm' h h'
end DeciSigma1.Holes.Fresh
