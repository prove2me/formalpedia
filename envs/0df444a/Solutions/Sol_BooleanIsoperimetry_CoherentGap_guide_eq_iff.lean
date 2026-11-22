-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.guide_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:29.652012+00:00
-- url     : https://prove2.me/submissions/072e01ea-8fb7-42f3-becc-4af4a2d45393

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
theorem _root_.solution {dimension width : ℕ} (hwidth : 0 < width) :
    guide dimension = width ↔
      triangular (width - 1) + 2 ≤ dimension ∧
        dimension ≤ triangular width + 1 := by
  unfold guide
  rw [Nat.find_eq_iff]
  constructor
  · intro ⟨hupper, hminimal⟩
    constructor
    · by_contra hnot
      have hsmall : dimension - 1 ≤ triangular (width - 1) := by omega
      exact hminimal (width - 1) (by omega) hsmall
    · omega
  · intro ⟨hlower, hupper⟩
    constructor
    · omega
    · intro smaller hsmaller
      have hle : smaller ≤ width - 1 := by omega
      have htriangular := triangular_mono hle
      omega
end BooleanIsoperimetry.CoherentGap
