-- Prove2me | solution 1 for BandParity.pm_gi_pow_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:04.260709+00:00
-- url     : https://prove2.me/submissions/33ed13a1-1075-4f1b-a595-577c18693b7e

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
theorem _root_.solution {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by
  obtain ⟨j, rfl⟩ := he
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_succ, pow_mul, hu2]
  rcases neg_one_pow_eq_or GaussianInt j with h | h <;> rw [h] <;> rcases hu with rfl | rfl <;>
    simp
end BandParity
