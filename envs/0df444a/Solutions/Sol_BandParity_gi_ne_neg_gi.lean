-- Prove2me | solution 1 for BandParity.gi_ne_neg_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:55.786301+00:00
-- url     : https://prove2.me/submissions/5267ab10-db55-4b3e-a04d-7e69d96bad28

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
theorem _root_.solution : gi ≠ -gi := by
  intro h; have := congrArg Zsqrtd.im h; simp at this
end BandParity
