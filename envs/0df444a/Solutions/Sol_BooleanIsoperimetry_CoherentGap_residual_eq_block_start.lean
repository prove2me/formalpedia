-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.residual_eq_block_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:29.20894+00:00
-- url     : https://prove2.me/submissions/30b05b92-9a81-495d-aa48-4a1422da4562

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
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_guide_eq_iff
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_residual_succ_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {width dimension : ℕ}
    (hwidth : 0 < width)
    (hguide : guide dimension = width) :
    residual width dimension =
      residual width (triangular (width - 1) + 2) := by
  obtain ⟨hlower, hupper⟩ := (guide_eq_iff hwidth).mp hguide
  induction dimension, hlower using Nat.le_induction with
  | base => rfl
  | succ dimension hbase inductionHypothesis =>
      have hnextGuide : guide (dimension + 1) = width :=
        (guide_eq_iff hwidth).mpr ⟨by omega, by omega⟩
      have htriangular := self_le_triangular (width - 1)
      have hwidthLe : width ≤ dimension := by omega
      have hcurrentGuide : guide dimension = width :=
        (guide_eq_iff hwidth).mpr ⟨hbase, by omega⟩
      rw [residual_succ_eq (by omega) hwidthLe hnextGuide,
        inductionHypothesis hcurrentGuide (by omega)]
end BooleanIsoperimetry.CoherentGap
