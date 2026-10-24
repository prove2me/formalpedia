-- Prove2me | solution 1 for AvramDividend.Classical.levy_positive_root_unrestricted_upcrossing_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:11:44.436236+00:00
-- url     : https://prove2.me/submissions/63ff38ec-ea6e-4a76-8d1a-092c83d0d383

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_uniform_grid_upcrossing_discount_bound
import Theorems.Thm_AvramDividend_Classical_levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by
  let mesh : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
  have hpos : ∀ n : ℕ, 0 < mesh n := by
    intro n
    exact pow_pos (by norm_num : (0 : ℝ≥0) < 1 / 2) n
  have hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)) := by
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0) < 1)
  have hgrid (n : ℕ) :
      (∫⁻ ω : Ω,
        let up := ⨅ k : ℕ,
          if z < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < (⊤ : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0 ∂P) ≤
        ENNReal.ofReal (Real.exp (-(φ * z))) := by
    exact levy_positive_root_uniform_grid_upcrossing_discount_bound
      X q hq φ hφ hroot z hz (mesh n) (hpos n)
  exact levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
    X q (le_of_lt hq) z mesh hpos hzero
    (ENNReal.ofReal (Real.exp (-(φ * z)))) hgrid
