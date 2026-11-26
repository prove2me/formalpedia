-- Prove2me | solution 1 for BandParity.pm_gi_pow_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:41.689695+00:00
-- url     : https://prove2.me/submissions/93967e92-e477-4e56-83f5-f55abd015047

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_sq
attribute [local simp] BandParity.gi_re
attribute [local simp] BandParity.gi_im

set_option autoImplicit true
@[expose] public section
public section
open BandParity
namespace BandParity
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_mul, hu2]
end BandParity
