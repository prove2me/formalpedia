-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_original_filtered_brownian_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:11:17.253884+00:00
-- url     : https://prove2.me/submissions/99fd84e1-5ee8-4ae8-9224-e35dade90804

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_sameSpace_brownian_filtered
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Construct the imported filtered Brownian driver directly from the original Avram source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∃ ℱr : Filtration ℝ mΩ,
        (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
        LevyStochCalc.Brownian.IsBrownianFiltration W ℱr ∧
        (∀ (t : ℝ) (ω : Ω),
          W.W t ω =
            (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) := by
  obtain ⟨W, hW⟩ :=
    avram_lsc_zerojump_original_sameSpace_brownian X hν hσ
  obtain ⟨ℱr, hℱr, hFiltered⟩ :=
    avram_lsc_sameSpace_brownian_filtered X W hW
  exact ⟨W, ℱr, hℱr, hFiltered, hW⟩

