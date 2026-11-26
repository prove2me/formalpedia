-- Prove2me | solution 1 for BandParity.quartic_apply_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:24.282818+00:00
-- url     : https://prove2.me/submissions/92a1a921-0888-4740-a5bf-65e16aea36a1

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_pm_gi_pow_two_mul
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_quartic_apply_generator
public import Theorems.Thm_BandParity_neg_one_eq_generator_pow
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
theorem _root_.solution (hp8 : p % 8 = 5) : χ (-1) = -1 := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  have hp2 : p ≠ 2 := by omega
  rw [← neg_one_eq_generator_pow hp2 hgo, Units.val_pow_eq_pow_val, map_pow,
    show (p - 1) / 2 = 2 * (2 * (p / 8) + 1) by omega,
    pm_gi_pow_two_mul (quartic_apply_generator χ hχ hg)]
  simp [pow_succ, pow_mul]
end BandParity
