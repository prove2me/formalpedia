-- Prove2me | solution 1 for BooleanIsoperimetry.union_initSeg_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:39:54.007422+00:00
-- url     : https://prove2.me/submissions/a278980a-7600-4e43-85db-e5bb855e1a00

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
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_card_initSeg_union
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b : ℕ} {B C : Finset (Cube n)}
    (hHa : (neighborhood 1 (simplicialInitSeg n a)).card ≤ (neighborhood 1 B).card)
    (hb : C.card = b) (hb2 : b ≤ 2 ^ n) :
    (neighborhood 1 (simplicialInitSeg n a) ∪ simplicialInitSeg n b).card ≤
      (neighborhood 1 B ∪ C).card := by
  have h_max : (neighborhood 1 (simplicialInitSeg n a) ∪ simplicialInitSeg n b).card ≤
      max (H n a) b := by
    rw [ neighborhood_initSeg_eq ];
    convert card_initSeg_union ( show H n a ≤ 2 ^ n from ?_ ) hb2 |> le_of_eq using 1;
    exact H_le_cube n a;
  refine h_max.trans ( max_le ?_ ?_ );
  · exact le_trans hHa ( Finset.card_mono ( Finset.subset_union_left ) );
  · exact hb ▸ Finset.card_le_card ( Finset.subset_union_right )
end BooleanIsoperimetry
