-- Prove2me | solution 2 for AvramDividend.Classical.avram_e0_initial_step_original_infinite_cap_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:49:03.968567+00:00
-- url     : https://prove2.me/submissions/90e04dd8-298f-4ccf-a2e4-13ba35559785

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! A source-exact admissible initial lump-sum, ready for the geometric mark witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKmeas : Measurable[𝓕 0] K)
    (hKle : ∀ ω, K ω ≤ x) :
    IsAdmissibleLe X x ⊤ (fun t ω => if t = 0 then 0 else K ω) := by
  apply avram_e0_initial_step_admissible_infinite_cap_of_rightLimit X x K
  · exact avram_e0_initial_only_isDividendStrategy 𝓕 K hKnonneg hKmeas
  · intro ω t
    exact avram_e0_initial_only_dividend_rightlimit K ω t
  · exact hKle
