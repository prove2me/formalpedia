-- Prove2me | solution 1 for CriticalPortraits.edgeStep_forced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:38:07.521388+00:00
-- url     : https://prove2.me/submissions/abd2b5ca-00c4-4bcc-9d07-644ce74d2157

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
public import Theorems.Thm_CriticalPortraits_predIn_forced

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
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P₁ P₂ : Finset (Finset (ZMod (d * m)))} (h₁ : Portrait d m P₁) (h₂ : Portrait d m P₂)
    (hT : T P₁ = T P₂) {u v : ZMod (d * m)} (hstep : edgeStep P₁ u v) : edgeStep P₂ u v := by
  obtain ⟨hu₁, hv₁, hcase⟩ := hstep
  have hu₂ : u ∈ T P₂ := hT ▸ hu₁
  have hv₂ : v ∈ T P₂ := hT ▸ hv₁
  refine ⟨hu₂, hv₂, ?_⟩
  rcases hcase with hpu | hpv
  · left; rw [← predIn_forced hd hm h₁ h₂ hT hu₁ hu₂]; exact hpu
  · right; rw [← predIn_forced hd hm h₁ h₂ hT hv₁ hv₂]; exact hpv
end CriticalPortraits
