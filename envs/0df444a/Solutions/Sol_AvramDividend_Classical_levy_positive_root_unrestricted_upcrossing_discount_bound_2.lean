-- Prove2me | solution 2 for AvramDividend.Classical.levy_positive_root_unrestricted_upcrossing_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:58:29.974776+00:00
-- url     : https://prove2.me/submissions/c9352728-c7a7-4a49-aa5f-4e679e8a3e16

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_uniform_grid_upcrossing_discount_bound
import Theorems.Thm_AvramDividend_Classical_levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
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
  have hpos (n : ℕ) : 0 < mesh n := by
    dsimp [mesh]
    exact pow_pos (by norm_num : (0 : ℝ≥0) < 1 / 2) n
  have hzero : Tendsto mesh atTop (nhds (0 : ℝ≥0)) := by
    dsimp [mesh]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 / 2 : ℝ≥0) < 1)
  exact AvramDividend.Classical.levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
    X q (le_of_lt hq) z mesh hpos hzero
    (ENNReal.ofReal (Real.exp (-(φ * z))))
    (fun n => AvramDividend.Classical.levy_positive_root_uniform_grid_upcrossing_discount_bound
      X q hq φ hφ hroot z hz (mesh n) (hpos n))
