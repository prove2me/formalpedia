-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.guide_at_triangular_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:44.35374+00:00
-- url     : https://prove2.me/submissions/ccda6dc2-f957-4f0f-8419-45b5a5541c1f

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_triangular_strictMono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (width : ℕ) :
    guide (triangular width + 1) = width := by
  unfold guide
  apply Nat.find_eq_iff (guideWitness (triangular width + 1)) |>.mpr
  constructor
  · omega
  · intro smaller hsmaller
    have hstrict := triangular_strictMono hsmaller
    omega
end BooleanIsoperimetry.CoherentGap
