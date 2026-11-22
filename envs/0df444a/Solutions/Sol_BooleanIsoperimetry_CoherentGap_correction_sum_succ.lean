-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.correction_sum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:52.25115+00:00
-- url     : https://prove2.me/submissions/79fb1f06-2140-49cd-ab26-5dcaef858797

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (previous : ℕ) :
    (∑ index : Fin (previous + 1),
        conwayGuyHeight (triangular index.val)) =
      (∑ index : Fin previous,
          conwayGuyHeight (triangular index.val)) +
        conwayGuyHeight (triangular previous) := by
  rw [Fin.sum_univ_eq_sum_range
      (fun index => conwayGuyHeight (triangular index)) (previous + 1),
    Fin.sum_univ_eq_sum_range
      (fun index => conwayGuyHeight (triangular index)) previous,
    Finset.sum_range_succ]
end BooleanIsoperimetry.CoherentGap
