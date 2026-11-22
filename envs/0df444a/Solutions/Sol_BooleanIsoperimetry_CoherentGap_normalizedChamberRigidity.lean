-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.normalizedChamberRigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:55.303431+00:00
-- url     : https://prove2.me/submissions/5d0a01f9-c3f9-4f2d-8dff-02359a0b5f25

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_coordinate_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation, IsLiftableUnit (tower.weights n) relation →
      1 ≤ realDot relation candidate) :
    ∀ coordinate, (tower.weights n coordinate : ℝ) ≤ candidate coordinate := by
  intro coordinate
  exact coordinate_lower_bound
    (recurrenceCertificates tower recurrence n coordinate) candidate hgap
end BooleanIsoperimetry.CoherentGap
