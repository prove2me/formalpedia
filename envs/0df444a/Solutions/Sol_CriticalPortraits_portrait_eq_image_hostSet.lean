-- Prove2me | solution 1 for CriticalPortraits.portrait_eq_image_hostSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.61382+00:00
-- url     : https://prove2.me/submissions/787c3843-b8bc-4292-ba34-0c561fb58ccb

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
public import Theorems.Thm_CriticalPortraits_hostSet_eq_of_mem_eraseMin
public import Theorems.Thm_CriticalPortraits_mem_T


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
theorem _root_.solution {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    P = (T P).attach.image (fun x => hostSet P x.1 x.2) := by
  apply Finset.ext
  intro S
  constructor
  · -- S ∈ P ⇒ S is some hostSet
    intro hS
    -- S has a survivor (card ≥ 2 ⇒ eraseMin nonempty)
    have hcard : 2 ≤ S.card := (hP.1 S hS).2
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hecard : (eraseMin S).card = S.card - 1 := eraseMin_card S hSne
    have hene : (eraseMin S).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxe⟩ := hene
    have hx : x ∈ T P := mem_T.mpr ⟨S, hS, hxe⟩
    rw [Finset.mem_image]
    refine ⟨⟨x, hx⟩, Finset.mem_attach _ _, ?_⟩
    exact hostSet_eq_of_mem_eraseMin hP hS hxe
  · -- image element ⇒ in P
    intro hS
    rw [Finset.mem_image] at hS
    obtain ⟨x, _, hxeq⟩ := hS
    rw [← hxeq]
    exact hostSet_mem x.2
end CriticalPortraits
