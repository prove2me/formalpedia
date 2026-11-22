-- Prove2me | solution 1 for CriticalPortraits.T_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:39:49.444507+00:00
-- url     : https://prove2.me/submissions/4c02b654-33e5-4929-b0f8-c960c2bf1406

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
public import Theorems.Thm_CriticalPortraits_portrait_eq_image_hostSet
public import Theorems.Thm_CriticalPortraits_hostSet_forced

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
theorem _root_.solution (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) : P₁ = P₂ := by
  have : NeZero (d*m) := ⟨by positivity⟩
  rw [portrait_eq_image_hostSet h₁, portrait_eq_image_hostSet h₂]
  -- The attach sets differ (T P₁ vs T P₂), so rewrite along hT and match the functions.
  apply Finset.ext
  intro S
  rw [Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx₁⟩, _, hSeq⟩
    have hx₂ : x ∈ T P₂ := hT ▸ hx₁
    refine ⟨⟨x, hx₂⟩, Finset.mem_attach _ _, ?_⟩
    rw [← hSeq]
    exact (hostSet_forced hd hm h₁ h₂ hT hx₁ hx₂).symm
  · rintro ⟨⟨x, hx₂⟩, _, hSeq⟩
    have hx₁ : x ∈ T P₁ := hT.symm ▸ hx₂
    refine ⟨⟨x, hx₁⟩, Finset.mem_attach _ _, ?_⟩
    rw [← hSeq]
    exact hostSet_forced hd hm h₁ h₂ hT hx₁ hx₂
end CriticalPortraits
