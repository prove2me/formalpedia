-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_suffixOccurrenceCuts_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:04.109622+00:00
-- url     : https://prove2.me/submissions/be34c640-aa0e-4399-98c3-f64ecaa0e5cb

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_prefixComparingCuts_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (j : Fin k) (z : List α) : (suffixOccurrenceCuts W j z).card ≤ Fintype.card S - 1 :=
  card_prefixComparingCuts_le (hfr j) z
end DeciSigma1.Holes.Fresh
