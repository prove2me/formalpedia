-- Prove2me | solution 1 for CriticalPortraits.span_laminar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:49.969322+00:00
-- url     : https://prove2.me/submissions/19a70491-0526-47b7-a6a3-e58e6b9b988b

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
public import Theorems.Thm_CriticalPortraits_maxVal_mem
public import Theorems.Thm_CriticalPortraits_linked_of_lt


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
    {A B : Finset (ZMod (d * m))} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ¬ (spanLo A hAne < spanLo B hBne ∧ spanLo B hBne < spanHi A hAne ∧
       spanHi A hAne < spanHi B hBne) := by
  rintro ⟨h1, h2, h3⟩
  -- the four endpoints minVal A < minVal B < maxVal A < maxVal B alternate ⇒ Linked A B
  simp only [spanLo, spanHi] at h1 h2 h3
  have hL : Linked A B :=
    linked_of_lt (minVal_mem A hAne) (maxVal_mem A hAne) (minVal_mem B hBne) (maxVal_mem B hBne)
      h1 h2 h3
  exact (hP.2.2.1 A hA B hB hAB) hL
end CriticalPortraits
