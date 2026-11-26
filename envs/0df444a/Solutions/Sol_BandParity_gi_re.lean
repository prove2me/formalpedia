-- Prove2me | solution 1 for BandParity.gi_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:51:27.446481+00:00
-- url     : https://prove2.me/submissions/18ad54de-39bd-473e-aee2-96fd6bbcb82a

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
theorem _root_.solution : gi.re = 0 := rfl
end BandParity
