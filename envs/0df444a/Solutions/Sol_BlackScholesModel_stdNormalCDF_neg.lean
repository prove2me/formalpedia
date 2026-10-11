-- Prove2me | solution 1 for BlackScholesModel.stdNormalCDF_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:45:01.257101+00:00
-- url     : https://prove2.me/submissions/8bf1588d-1664-4404-a0ef-3850116a9c9c

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (x : ℝ) :
    stdNormalCDF (-x) = 1 - stdNormalCDF x := by
  let f : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / 2)
  have heq : f = (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
    funext z
    dsimp [f]
    congr 1
    ring
  have hf : Integrable f volume := by
    rw [heq]
    exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have htotal : (∫ z : ℝ, f z) = Real.sqrt (2 * Real.pi) := by
    rw [heq, integral_gaussian (1 / 2 : ℝ)]
    congr 1
    ring
  have heven : (fun z : ℝ => f (-z)) = f := by
    funext z
    dsimp [f]
    congr 1
    ring
  have hmirror :
      (∫ z in Set.Iic (-x), f z) =
        (∫ z in Set.Ioi x, f z) := by
    simpa only [heven, neg_neg] using (integral_comp_neg_Iic (-x) f)
  have hpartition :
      (∫ z in Set.Iic x, f z) +
        (∫ z in Set.Ioi x, f z) = ∫ z : ℝ, f z :=
    intervalIntegral.integral_Iic_add_Ioi
      (hf.integrableOn) (hf.integrableOn)
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hmass : (1 / Real.sqrt (2 * Real.pi)) *
      Real.sqrt (2 * Real.pi) = 1 := by
    field_simp [hsqrt]
  unfold stdNormalCDF
  change (1 / Real.sqrt (2 * Real.pi)) *
      (∫ z in Set.Iic (-x), f z) =
      1 - (1 / Real.sqrt (2 * Real.pi)) *
        (∫ z in Set.Iic x, f z)
  rw [hmirror]
  calc
    (1 / Real.sqrt (2 * Real.pi)) * (∫ z in Set.Ioi x, f z) =
        (1 / Real.sqrt (2 * Real.pi)) *
          ((∫ z : ℝ, f z) - (∫ z in Set.Iic x, f z)) := by
            congr 1
            linarith [hpartition]
    _ = 1 - (1 / Real.sqrt (2 * Real.pi)) *
          (∫ z in Set.Iic x, f z) := by
          rw [htotal, mul_sub, hmass]
