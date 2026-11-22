-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.conwayGuy_block_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:36.044805+00:00
-- url     : https://prove2.me/submissions/d0ecb05f-5ec0-4a54-ab24-4edcab252c86

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_block_identity_by_width
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (dimension : ℕ)
    (hdimension : 2 ≤ dimension) :
    conwayGuyHeight dimension -
          ∑ index : Fin (guide dimension),
            conwayGuyHeight (dimension - index.val - 1) +
        ∑ index : Fin (guide dimension - 1),
          conwayGuyHeight (triangular index.val) = 1 := by
  have hwidth := guide_pos hdimension
  have hguide :
      guide dimension - 1 + 1 = guide dimension := by
    omega
  have hidentity :=
    block_identity_by_width (guide dimension - 1) dimension hguide.symm
  rw [hguide] at hidentity
  simpa only [residual] using hidentity
end BooleanIsoperimetry.CoherentGap
