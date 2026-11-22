-- Prove2me | solution 1 for CriticalPortraits.minVal_host_not_mem_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:50.924799+00:00
-- url     : https://prove2.me/submissions/d87062d6-d819-4cfb-8c16-9c4f2116b8e0

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
public import Theorems.Thm_CriticalPortraits_mem_T
public import Theorems.Thm_CriticalPortraits_mem_eraseMin


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
theorem _root_.solution {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {x : ZMod (d * m)} (hx : x ∈ T P) (hne : (hostSet P x hx).Nonempty) :
    minVal (hostSet P x hx) hne ∉ T P := by
  intro hmem
  set S := hostSet P x hx with hSdef
  set w := minVal S hne with hwdef
  have hSP : S ∈ P := hostSet_mem hx
  have hwS : w ∈ S := minVal_mem S hne
  obtain ⟨S', hS'P, hwS'⟩ := mem_T.mp hmem
  have hwS'S : w ∈ S' := eraseMin_subset S' hwS'
  have hSS' : S = S' := by
    by_contra hne'
    exact (Finset.disjoint_left.mp (hP.2.1 _ hSP _ hS'P hne') hwS) hwS'S
  rw [← hSS'] at hwS'
  exact ((mem_eraseMin S hne w).mp hwS').2 rfl
end CriticalPortraits
