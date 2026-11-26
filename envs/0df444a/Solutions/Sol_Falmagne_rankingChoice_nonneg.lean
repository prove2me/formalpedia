-- Prove2me | solution 1 for Falmagne.rankingChoice_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:16.509806+00:00
-- url     : https://prove2.me/submissions/a0af18b9-14c9-4475-9671-fd43fbd37bba

module
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Basic

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x y : X}
namespace Falmagne
theorem _root_.solution (l : List X) (A : Finset X) (x : X) :
    0 ≤ rankingChoice l A x := by
  unfold rankingChoice
  split <;> norm_num
end Falmagne
