-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:34:20.800219+00:00
-- url     : https://prove2.me/submissions/2c12c901-7fa9-4e4d-90d7-2bb22503a457

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_horizon_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical strict-left-limit value has finite L1 from a common
all-horizon value envelope and fixed-time source measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T t : ℝ≥0) (ht : t ≤ T)
    (hMeas : AEStronglyMeasurable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P) :
    Integrable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P := by
  obtain ⟨K, hK, hbound⟩ :=
    AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_horizon_envelope
      X hBV x D hD w hw_cont hw_neg T
  letI : IsProbabilityMeasure P := X.isProbability
  have hNorm : ∀ᵐ ω ∂P,
      ‖w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)‖ ≤ K := by
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω t ht
  exact (integrable_const K).mono' hMeas hNorm
