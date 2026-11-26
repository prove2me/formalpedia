-- Prove2me | solution 1 for BandParity.quartic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:12.722203+00:00
-- url     : https://prove2.me/submissions/00c5a787-aa31-4ab3-9a5f-2054b54909b5

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_eq_of_pow_four_eq_one
public import Theorems.Thm_BandParity_unit_apply_pow_four
attribute [local simp] BandParity.gi_re
attribute [local simp] BandParity.gi_im

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi :=
  eq_of_pow_four_eq_one (by simpa using unit_apply_pow_four χ hχ (Units.mk0 a ha))
end BandParity
