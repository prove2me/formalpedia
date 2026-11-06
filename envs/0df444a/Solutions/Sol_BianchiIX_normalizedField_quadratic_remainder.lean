-- Prove2me | solution 1 for BianchiIX.normalizedField_quadratic_remainder
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:18:49.6623+00:00
-- url     : https://prove2.me/submissions/64f4934d-9660-43a7-be8b-c842110efabc

import Definitions.Def_BianchiIX_Dynamics_Linearization
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.hasFDerivAt_normalizedField (x : NormalizedState) :
    HasFDerivAt normalizedField (normalizedDifferential x) x :=
  ((contDiff_normalizedField 1).differentiable (by norm_num) x).hasFDerivAt

/-- A uniform quadratic Taylor bound, without selecting second derivative coordinates. -/
theorem solution {S : Set NormalizedState} (hS : Convex ℝ S)
    {K : ℝ≥0} (hK : LipschitzOnWith K normalizedDifferential S)
    {x y : NormalizedState} (hx : x ∈ S) (hy : y ∈ S) :
    ‖normalizedField y - normalizedField x - normalizedDifferential x (y - x)‖ ≤
      K * ‖y - x‖ ^ 2 := by
  let g : NormalizedState → NormalizedState := fun z => normalizedField z - normalizedDifferential x z
  have hg (z : NormalizedState) :
      HasFDerivAt g (normalizedDifferential z - normalizedDifferential x) z :=
    (hasFDerivAt_normalizedField z).sub (normalizedDifferential x).hasFDerivAt
  have hbound (z : NormalizedState) (hz : z ∈ segment ℝ x y) :
      ‖normalizedDifferential z - normalizedDifferential x‖ ≤ K * ‖y - x‖ :=
    (hK.norm_sub_le (hS.segment_subset hx hy hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g, map_sub, sub_sub_sub_comm, pow_two, mul_assoc] using H
