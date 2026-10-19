-- Prove2me | solution 1 for Ehrhart.BergmanGeodesicConvexity.exponentialMoment_sq_le_partition_mul_second
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/809e3e70-e44c-4e27-90c3-92eef9166971

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanGeodesicConvexity
open Set Module
open scoped BigOperators InnerProductSpace
namespace Ehrhart.BergmanGeodesicConvexity
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    exponentialMoment w order 1 t ^ 2 ≤
      exponentialPartition w order t *
        exponentialMoment w order 2 t := by
  classical
  let a : ι → ℝ := fun i =>
    w i * Real.exp (t * (order i : ℝ))
  have ha : ∀ i, 0 ≤ a i := fun i =>
    mul_nonneg (hw i) (Real.exp_pos _).le
  have hcauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset ι)
    (r := fun i => a i * (order i : ℝ))
    (f := a)
    (g := fun i => a i * (order i : ℝ) ^ 2)
    (fun i _ => ha i)
    (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
    (fun i _ => (by ring : (a i * (order i : ℝ)) ^ 2 =
      a i * (a i * (order i : ℝ) ^ 2)).le)
  simpa [exponentialMoment, exponentialPartition, a,
    mul_assoc, mul_left_comm, mul_comm] using hcauchy
end Ehrhart.BergmanGeodesicConvexity
