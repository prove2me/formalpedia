-- Prove2me | solution 1 for BooleanIsoperimetry.macaulay_extremal_pos_step_GT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:04.220855+00:00
-- url     : https://prove2.me/submissions/46f41785-bfd1-4e5f-ad0f-25cf341f84e8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Theorems.Thm_BooleanIsoperimetry_H_shadow_GT_sum


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (_ : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (_ : p ≤ 2 ^ n) (_ : q ≤ 2 ^ n)
    (_ : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) (hq_pos : 1 ≤ q)
    (hba : b ≤ a) (hcase : H n b < a) :
    H n p + H n q ≤ H n a + a :=
  H_shadow_GT_sum ha hb hcasc hq_pos hba hcase
end BooleanIsoperimetry
