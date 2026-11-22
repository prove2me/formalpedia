-- Prove2me | solution 1 for CriticalPortraits.Defc_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:14.19873+00:00
-- url     : https://prove2.me/submissions/1f8a56ef-6f9b-482d-bc57-0679a0881d81

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
public import Theorems.Thm_CriticalPortraits_Scount_antitone_left

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (_hm : 0 < m) (U : Finset (ZMod (d * m))) (φ lu uval k : ℕ) :
    Defc U φ lu uval (k+1) ≤ Defc U φ lu uval k + 1 := by
  unfold Defc
  have hmono : Scount U (φ + (k+1)*m) uval ≤ Scount U (φ + k*m) uval := by
    apply Scount_antitone_left
    simp_all
  have h1 : (Scount U (φ + (k+1)*m) uval : ℤ) ≤ (Scount U (φ + k*m) uval : ℤ) := by
    exact_mod_cast hmono
  push_cast
  omega
end CriticalPortraits
