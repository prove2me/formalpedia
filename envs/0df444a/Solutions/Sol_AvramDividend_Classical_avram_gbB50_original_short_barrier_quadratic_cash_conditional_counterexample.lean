-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB50_original_short_barrier_quadratic_cash_conditional_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:51:15.038061+00:00
-- url     : https://prove2.me/submissions/3418be45-fc66-4145-a329-9c3b729092b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_short_horizon_cash_identity_contradiction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Conditional source-faithful short-horizon original quadratic cash contradiction. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
  (hT : 0 < T)
  (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
  (F N : ℝ)
  (hCash : F - (3 / 16 : ℝ) - N =
    (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
    Real.exp (-(1 / 100000 : ℝ)) *
      (riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω -
        4 * (riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω) ^ 2 -
        15 / 242) - (1 / 1936 : ℝ)) :
  sInf ((Icc (0 : ℝ≥0) T ∩
    (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
      Ici (-(5 / 44 : ℝ))) ∪ {T}) = T ∧
  ¬ F - (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by
  have hCapNN :=
    barrierStrategy_reserve_cap_bound_all_capital
      X (1 / 8 : ℝ) (1 / 8 : ℝ)
      (by norm_num) (by norm_num) ω T hT
  have hCap : riskProcess X (1 / 8 : ℝ)
      (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
      (1 / 8 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp hCapNN
  have hFloor := avram_gbB38_barrier_reserve_above_cutoff_on_tube X T ω hTube
  constructor
  · exact avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube X T ω hTube
  · exact avram_gbB39_short_horizon_cash_identity_contradiction
      (riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω)
      F (3 / 16 : ℝ) N (le_of_lt hFloor) hCap hCash
