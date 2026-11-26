-- Prove2me | solution 1 for BandParity.unit_apply_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:48.096205+00:00
-- url     : https://prove2.me/submissions/55ac2916-6d4a-49c9-85ac-191fad716881

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
theorem _root_.solution {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one, MulChar.one_apply_coe]
end BandParity
