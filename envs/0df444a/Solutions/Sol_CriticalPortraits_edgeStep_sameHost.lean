-- Prove2me | solution 1 for CriticalPortraits.edgeStep_sameHost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:08.956621+00:00
-- url     : https://prove2.me/submissions/bea2fa14-d9d1-4c64-8a6d-ad3258682de5

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
public import Theorems.Thm_CriticalPortraits_hostSet_eq_of_mem

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
    {u v : ZMod (d * m)} (hstep : edgeStep P u v) (hu : u ∈ T P) (hv : v ∈ T P) :
    hostSet P u hu = hostSet P v hv := by
  obtain ⟨hu', hv', hcase⟩ := hstep
  rcases hcase with hpu | hpv
  · have : v ∈ hostSet P u hu := by rw [← hpu]; exact predIn_mem_host hu
    exact (hostSet_eq_of_mem hP hv (hostSet_mem hu) this).symm
  · have : u ∈ hostSet P v hv := by rw [← hpv]; exact predIn_mem_host hv
    exact hostSet_eq_of_mem hP hu (hostSet_mem hv) this
end CriticalPortraits
