-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_step_original_infinite_cap_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:47:02.233081+00:00
-- url     : https://prove2.me/submissions/1c04e45a-4b05-439b-b417-85bba3552e6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Assemble the published initial step strategy, right limit, and
    infinite-cap admissibility, preserving the original Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKmeas : Measurable[𝓕 0] K)
    (hKle : ∀ ω, K ω ≤ x) :
    IsAdmissibleLe X x ⊤ (fun t ω => if t = 0 then 0 else K ω) := by
  exact avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
    X x K
    (avram_e0_initial_only_isDividendStrategy 𝓕 K hKnonneg hKmeas)
    (fun ω t => avram_e0_initial_only_dividend_rightlimit K ω t)
    hKle
