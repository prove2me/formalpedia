-- Prove2me | solution 1 for BooleanIsoperimetry.card_le_of_hDist_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:20.243077+00:00
-- url     : https://prove2.me/submissions/f41d937c-7ce1-4ffe-a071-92cffbe18a97

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r : ℕ} {u x : Cube N} (hu : u.card = r) (hd : hDist u x ≤ 1) :
    x.card ≤ r + 1 := by
  unfold hDist at hd
  have hsub : x \ u ⊆ symmDiff u x := by
    intro y hy
    rw [Finset.mem_sdiff] at hy
    rw [Finset.mem_symmDiff]
    exact Or.inr hy
  have hcard1 : (x \ u).card ≤ 1 := le_trans (Finset.card_mono hsub) hd
  have hx : x.card ≤ (x \ u).card + u.card := Finset.card_le_card_sdiff_add_card
  omega
end BooleanIsoperimetry
