-- Prove2me | solution 1 for BandParity.gi_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:28.517189+00:00
-- url     : https://prove2.me/submissions/ae0f4411-faa3-445b-9b76-2d0960a8cf9d

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic

set_option autoImplicit true
@[expose] public section
public section
open BandParity
namespace BandParity
theorem _root_.solution : gi.im = 1 := rfl
end BandParity
