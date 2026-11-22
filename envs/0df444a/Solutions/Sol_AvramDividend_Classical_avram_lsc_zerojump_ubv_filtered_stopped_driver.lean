-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_ubv_filtered_stopped_driver
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:55:02.329188+00:00
-- url     : https://prove2.me/submissions/e1ee53a0-97e9-43ca-841c-b49550ec67e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_sameSpace_brownian_filtered
import Theorems.Thm_AvramDividend_Classical_avram_lsc_nnreal_stopping_to_real_clock
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original-space filtered Brownian driver and stopped clock under Avram's UBV hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∃ ℱr : Filtration ℝ mΩ,
        (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
        LevyStochCalc.Brownian.IsBrownianFiltration W ℱr ∧
        (∀ (t : ℝ) (ω : Ω),
          W.W t ω =
            (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) ∧
        IsStoppingTime ℱr
          (fun ω => ((τ ω : ℝ) : WithTop ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν
  obtain ⟨W, hW⟩ :=
    avram_lsc_zerojump_original_sameSpace_brownian X hν hσ
  obtain ⟨ℱr, hℱr, hFiltered⟩ :=
    avram_lsc_sameSpace_brownian_filtered X W hW
  have hClock : IsStoppingTime ℱr
      (fun ω => ((τ ω : ℝ) : WithTop ℝ)) :=
    avram_lsc_nnreal_stopping_to_real_clock ℱr hℱr τ hτ
  exact ⟨W, ℱr, hℱr, hFiltered, hW, hClock⟩

