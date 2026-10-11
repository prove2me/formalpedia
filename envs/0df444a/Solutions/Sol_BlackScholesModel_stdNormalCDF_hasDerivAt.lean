-- Prove2me | solution 1 for BlackScholesModel.stdNormalCDF_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T13:45:57.624574+00:00
-- url     : https://prove2.me/submissions/deedefde-49cf-4cae-b320-4f325891901b

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (x : ℝ) :
    HasDerivAt stdNormalCDF (stdNormalPDF x) x := by
  let f : ℝ → ℝ := fun z => Real.exp (-z ^ 2 / 2)
  have hf : Integrable f volume := by
    have hbase : Integrable (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) volume :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase using 1
    funext z
    dsimp [f]
    congr 1
    ring
  have hc : Continuous f := by
    dsimp [f]
    fun_prop
  have hFTC : HasDerivAt (fun u : ℝ => ∫ z in (0 : ℝ)..u, f z) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable)
      (hc.stronglyMeasurableAtFilter volume (nhds x))
      hc.continuousAt
  have hIic_eq :
      (fun u : ℝ => ∫ z in Set.Iic u, f z) =
      (fun u : ℝ => (∫ z in Set.Iic (0 : ℝ), f z) +
        ∫ z in (0 : ℝ)..u, f z) := by
    funext u
    have hsub : (∫ z in Set.Iic u, f z) -
        (∫ z in Set.Iic (0 : ℝ), f z) =
        ∫ z in (0 : ℝ)..u, f z :=
      intervalIntegral.integral_Iic_sub_Iic hf.integrableOn hf.integrableOn
    linarith
  have hprimitive : HasDerivAt (fun u : ℝ => ∫ z in Set.Iic u, f z) (f x) x := by
    rw [hIic_eq]
    exact hFTC.const_add _
  have hresult := hprimitive.const_mul (1 / Real.sqrt (2 * Real.pi))
  convert hresult using 1 <;> (first | rfl | simp only [stdNormalCDF, stdNormalPDF, f] | ring)
