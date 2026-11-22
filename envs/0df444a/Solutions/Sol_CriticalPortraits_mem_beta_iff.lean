-- Prove2me | solution 1 for CriticalPortraits.mem_beta_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:08.257992+00:00
-- url     : https://prove2.me/submissions/cb0ba7ff-fa36-41a4-9a47-037b611ab154

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {S : Finset (ZMod (d * m))} :
    S ∈ beta U ↔ ∃ v ∈ bVerts U, betaBlock U v = S := by
  unfold beta; rw [Finset.mem_image]
end CriticalPortraits
