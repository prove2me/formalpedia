-- Prove2me | solution 1 for BlackScholesModel.stdNormalCDF_tail_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:22:53.463992+00:00
-- url     : https://prove2.me/submissions/b00e51d5-4363-4363-ba6c-e63a800379f2

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution :
    Tendsto stdNormalCDF atBot (𝓝 0) ∧
    Tendsto stdNormalCDF atTop (𝓝 1) := by
  have hIic :
      Tendsto
        (fun x : ℝ => ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2))
        atBot (𝓝 0) :=
    MeasureTheory.tendsto_integral_Iic_zero tendsto_id
  have hbot : Tendsto stdNormalCDF atBot (𝓝 0) := by
    change Tendsto (fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) *
      ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2)) atBot (𝓝 0)
    simpa only [mul_zero] using
      hIic.const_mul (1 / Real.sqrt (2 * Real.pi))
  have hneg : Tendsto (fun x : ℝ => -x) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot
  have hnegCDF : Tendsto
      (fun x : ℝ => stdNormalCDF (-x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using hbot.comp hneg
  have htopRaw : Tendsto
      (fun x : ℝ => 1 - stdNormalCDF (-x)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hnegCDF)
  have hfun :
      (fun x : ℝ => 1 - stdNormalCDF (-x)) = stdNormalCDF := by
    funext x
    simpa only [neg_neg] using (stdNormalCDF_neg (-x)).symm
  exact ⟨hbot, by simpa only [hfun] using htopRaw⟩