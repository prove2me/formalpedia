-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_original_single_reset_isDividendStrategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:40:47.227871+00:00
-- url     : https://prove2.me/submissions/88c8f736-3b38-4296-88cf-73e6ccfbf21a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_reset_amount_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_adapted_of_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_dividend_strategy_of_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual Levy reserve clipped at a deterministic clock defines an
original adapted, monotone, left-continuous dividend strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (s : ℝ≥0) :
    IsDividendStrategy 𝓕 (fun t ω =>
      if t ≤ s then 0 else max (x + X.X s ω) (0 : ℝ)) := by
  let K : Ω → ℝ := fun ω => max (x + X.X s ω) (0 : ℝ)
  have hK : ∀ ω, 0 ≤ K ω := by
    intro ω
    exact le_max_right _ _
  have hKmeas : Measurable[𝓕 s] K :=
    avram_bv_tail13_original_reset_amount_clock_measurable X x s
  have hAdapt : Adapted 𝓕 (fun t ω => if t ≤ s then 0 else K ω) :=
    avram_bv_tail13_single_step_adapted_of_clock_measurable 𝓕 s K hKmeas
  exact avram_bv_tail13_single_step_dividend_strategy_of_adapted
    𝓕 (fun t ω => if t ≤ s then 0 else K ω) s K
    hK (by intro t ω; rfl) hAdapt
