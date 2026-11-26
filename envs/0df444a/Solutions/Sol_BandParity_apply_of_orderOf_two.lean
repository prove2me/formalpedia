-- Prove2me | solution 1 for BandParity.apply_of_orderOf_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:56.753571+00:00
-- url     : https://prove2.me/submissions/4edcee72-f056-4fa2-8f23-09c11b413fd3

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : a = 0
  · left; rw [ha]; exact MulChar.map_zero χ
  · right
    have : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one]
      exact MulChar.one_apply (Ne.isUnit ha)
    exact mul_self_eq_one_iff.1 this
end BandParity
