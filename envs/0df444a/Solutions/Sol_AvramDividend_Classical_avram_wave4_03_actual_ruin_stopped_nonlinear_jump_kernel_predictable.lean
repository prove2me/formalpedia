-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_ruin_stopped_nonlinear_jump_kernel_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:45:42.123428+00:00
-- url     : https://prove2.me/submissions/cfbb8ec5-4173-4f73-84dd-70e18a0837aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine endogenous ruin stopping (inclusive) of the original Lévy
nonlinear pre-jump marked kernel; no external PRM assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
        (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
         w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))) := by
  exact avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
    X x D hD w hw (ruinTime X x D)
    (avram_wave4_03_actual_ruinTime_rightCont_stopping_time X x D hD)
