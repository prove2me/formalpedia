-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB48_original_short_barrier_clock_cash_strict_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:45:46.776199+00:00
-- url     : https://prove2.me/submissions/f11e4e25-df5e-4183-b923-dbf39ead260c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_short_horizon_cash_identity_contradiction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Conditional original barrier clock and cash excess certificate. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
  (hTube : ∀ s : ℝ≥0, s ≤ T → |X.X s ω| ≤ (1 / 400 : ℝ))
  (hYhi : riskProcess X (1 / 8 : ℝ)
    (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤ (1 / 8 : ℝ))
  (F N : ℝ)
  (hCash : F - (1 / 8 : ℝ) - N =
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
  ¬ F - (1 / 8 : ℝ) ≤ N + (1 / 1936 : ℝ) := by
  constructor
  · exact avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
      X T ω hTube
  · have hylo := avram_gbB38_barrier_reserve_above_cutoff_on_tube
      X T ω hTube
    exact avram_gbB39_short_horizon_cash_identity_contradiction
      (riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω)
      F (1 / 8 : ℝ) N (le_of_lt hylo) hYhi hCash
