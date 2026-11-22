-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_ubv_original_affine_brownian_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:55:02.574643+00:00
-- url     : https://prove2.me/submissions/b9c90e62-f7f6-4a91-96b8-02312aa0eb4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original-space real-time drift plus Gaussian driver identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        X.X (Real.toNNReal t) ω =
          (Real.toNNReal t : ℝ) * X.c + X.σ * W.W t ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν
  obtain ⟨W, hW⟩ :=
    avram_lsc_zerojump_original_sameSpace_brownian X hν hσ
  refine ⟨W, ?_⟩
  intro t ω
  rw [hW t ω]
  field_simp [ne_of_gt hσ]
  ring

