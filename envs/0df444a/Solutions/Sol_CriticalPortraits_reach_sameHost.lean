-- Prove2me | solution 1 for CriticalPortraits.reach_sameHost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:49.07584+00:00
-- url     : https://prove2.me/submissions/998e1af8-95e9-4a12-87f3-cd9d871efda9

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_CriticalPortraits_edgeStep_sameHost

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x z : ZMod (d * m)} (hx : x ∈ T P)
    (hreach : Relation.ReflTransGen (edgeStep P) x z) (hz : z ∈ T P) :
    hostSet P z hz = hostSet P x hx := by
  induction hreach with
  | refl => rfl
  | @tail b c hxb hbc ih =>
    obtain ⟨hb, hc', hcase⟩ := hbc
    have hbc_host : hostSet P b hb = hostSet P c hc' :=
      edgeStep_sameHost hP ⟨hb, hc', hcase⟩ hb hc'
    simp_all
end CriticalPortraits
