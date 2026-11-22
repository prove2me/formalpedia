-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.negative_index_ge_guide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:12.092419+00:00
-- url     : https://prove2.me/submissions/5407c85d-af1a-48af-975a-bfaeb2690237

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {dimension index : ℕ}
    (hdimension : 2 ≤ dimension)
    (hindex : index < guide dimension - 1) :
    guide dimension ≤ dimension - triangular index - 1 := by
  have hwidth : 2 ≤ guide dimension := by omega
  have hindex_le : index ≤ guide dimension - 2 := by omega
  have htriangular :=
    triangular_mono hindex_le
  have hlower := guide_lower hdimension
  have hstep :
      triangular (guide dimension - 1) =
        triangular (guide dimension - 2) + (guide dimension - 1) := by
    have : guide dimension - 1 = (guide dimension - 2) + 1 := by omega
    conv_lhs => rw [this, triangular]
    omega
  omega
end BooleanIsoperimetry.CoherentGap
