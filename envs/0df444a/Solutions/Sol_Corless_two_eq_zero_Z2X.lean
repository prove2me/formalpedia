-- Prove2me | solution 1 for Corless.two_eq_zero_Z2X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:46.36295+00:00
-- url     : https://prove2.me/submissions/bb235d8b-9e1c-40bd-a087-29c0a0b95b01

module
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_LeanPool_CorlessNilpotent_Path
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity

set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
end Corless
