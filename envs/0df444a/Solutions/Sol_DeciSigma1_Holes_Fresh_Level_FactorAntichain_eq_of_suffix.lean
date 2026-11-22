-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.FactorAntichain.eq_of_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:19.452555+00:00
-- url     : https://prove2.me/submissions/27abee80-6a99-47eb-bcb9-8095910c3c72

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Fresh.Level
namespace FactorAntichain
theorem _root_.solution (hA : L.FactorAntichain) {m m' : Fin k} (hm : m ∈ L.active)
    (hm' : m' ∈ L.active)
    {u : List α} (h : L.marker m <:+ u) (h' : L.marker m' <:+ u) : L.marker m = L.marker m' := by
  rcases List.suffix_or_suffix_of_suffix h h' with h1 | h1
  · exact hA.2 m hm m' hm' h1.isInfix
  · exact (hA.2 m' hm' m hm h1.isInfix).symm
end FactorAntichain
end DeciSigma1.Holes.Fresh.Level
