-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:55:08.143232+00:00
-- url     : https://prove2.me/submissions/ea923da8-5ab9-4cb9-a1cc-2cd8c46b8463

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
open MeasureTheory ProbabilityTheory Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The controlled zero-jump reserve is Brownian drift minus its finite-variation dividends,
and its sample paths are left-continuous almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * W.W (t : ℝ) ω - D t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => riskProcess X x D u ω)
          (Set.Iic t) t) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσ : 0 < X.σ :=
    avram_p4_f4_zero_levy_ubv_sigma_pos X hBV hν
  obtain ⟨W, hW⟩ :=
    avram_lsc_zerojump_original_sameSpace_brownian X hν hσ
  refine ⟨W, ?_, ?_⟩
  · intro t ω
    have hrepr := hW (t : ℝ) ω
    simp only [Real.toNNReal_coe] at hrepr
    dsimp [riskProcess]
    rw [hrepr]
    field_simp [ne_of_gt hσ]
    ring
  · filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
      with ω hX
    intro t
    change ContinuousWithinAt
      (fun u : ℝ≥0 => x + X.X u ω - D u ω) (Iic t) t
    have hDLeft : ContinuousWithinAt
        (fun u : ℝ≥0 => D u ω) (Iic t) t :=
      hD.1.1.2.2.1 ω t
    exact (continuousWithinAt_const.add hX.continuousWithinAt).sub hDLeft

