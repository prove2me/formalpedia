-- Prove2me | solution 1 for BandParity.quartic_apply_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:21.727945+00:00
-- url     : https://prove2.me/submissions/93589a6d-0e88-4ef7-9c31-ed819a4147c2

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_pm_gi_pow_odd
public import Theorems.Thm_BandParity_exists_generator
public import Theorems.Thm_BandParity_quartic_apply_generator
public import Theorems.Thm_BandParity_two_eq_generator_pow_odd

set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  obtain ⟨e, he, h2⟩ := two_eq_generator_pow_odd hp8 hg
  rw [← h2, Units.val_pow_eq_pow_val, map_pow]
  exact pm_gi_pow_odd (quartic_apply_generator χ hχ hg) he
end BandParity
