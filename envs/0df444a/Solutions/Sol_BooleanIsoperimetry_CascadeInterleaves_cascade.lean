-- Prove2me | solution 1 for BooleanIsoperimetry.CascadeInterleaves.cascade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:17:58.632859+00:00
-- url     : https://prove2.me/submissions/d93c3c69-a543-4437-9e25-29018e165091

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
namespace CascadeInterleaves
theorem _root_.solution {n p q a b : ℕ}
    (h_inter : CascadeInterleaves n p q a b) :
    CascadeSplit n (a + b) p q :=
  h_inter.1
end CascadeInterleaves
end BooleanIsoperimetry
