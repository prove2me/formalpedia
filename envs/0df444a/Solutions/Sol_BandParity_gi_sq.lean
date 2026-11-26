-- Prove2me | solution 1 for BandParity.gi_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:52:07.806054+00:00
-- url     : https://prove2.me/submissions/5b8ab73c-2bf6-46e4-992d-944827c50c4e

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
theorem _root_.solution : gi ^ 2 = -1 := by
  rw [Zsqrtd.ext_iff]; simp [sq, gi]
end BandParity
