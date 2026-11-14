-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_clipped_prefix_survival_ruin_guard_redundant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:06:28.750562+00:00
-- url     : https://prove2.me/submissions/33d702a2-3c48-45e4-8410-7017394fd64c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ≥0) (hS : (S : ℝ) = T)
    (hSurvival : (S : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (t : ℝ≥0)
    (hPrefix : (t : ℝ) < T - T / ((n : ℝ) + 2)) :
    (t : ℝ≥0∞) ≤ ruinTime X x D ω  := by
  have hDelta : 0 ≤ T / ((n : ℝ) + 2) := by positivity
  have htT : (t : ℝ) ≤ T :=
    le_of_lt (lt_of_lt_of_le hPrefix (sub_le_self T hDelta))
  have htS : t ≤ S :=
    NNReal.coe_le_coe.mp (by simpa only [hS] using htT)
  exact (ENNReal.coe_le_coe.mpr htS).trans hSurvival.le
