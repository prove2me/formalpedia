-- Prove2me | solution 1 for BooleanIsoperimetry.H_shadow_LE_sum_as_upperShadow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:14.475006+00:00
-- url     : https://prove2.me/submissions/b6c0f8b5-cbf1-4b82-ac30-5f067d3064dc

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_H_shadow_closed_form

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b p q ra rb rp rq ta tb tp tq : ℕ}
    (hra : 1 ≤ ra) (hrb : 1 ≤ rb) (hrp : 1 ≤ rp) (hrq : 1 ≤ rq)
    (hae : a = binomPrefix N ra + ta) (hbe : b = binomPrefix N rb + tb)
    (hpe : p = binomPrefix N rp + tp) (hqe : q = binomPrefix N rq + tq) :
    (H N p + H N q ≤ H N a + H N b) ↔
      (binomPrefix N (rp + 1) + upperShadow N rp tp)
        + (binomPrefix N (rq + 1) + upperShadow N rq tq)
      ≤ (binomPrefix N (ra + 1) + upperShadow N ra ta)
        + (binomPrefix N (rb + 1) + upperShadow N rb tb) := by
  subst hae hbe hpe hqe
  rw [H_shadow_closed_form N ra ta hra, H_shadow_closed_form N rb tb hrb,
      H_shadow_closed_form N rp tp hrp, H_shadow_closed_form N rq tq hrq]
end BooleanIsoperimetry
