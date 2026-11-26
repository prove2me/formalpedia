-- Prove2me | solution 1 for BandParity.neg_one_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:53:02.917208+00:00
-- url     : https://prove2.me/submissions/c2d88eef-b493-4a1d-a035-a1d64cb1d112

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_gi_im
attribute [local simp] BandParity.gi_re
attribute [local simp] BandParity.gi_im

set_option autoImplicit true
@[expose] public section
public section
open BandParity
namespace BandParity
theorem _root_.solution : (-1 : GaussianInt) ≠ 1 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this
end BandParity
