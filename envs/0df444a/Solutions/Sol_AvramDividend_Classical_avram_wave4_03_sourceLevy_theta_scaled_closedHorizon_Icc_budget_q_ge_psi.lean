-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_budget_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:36:50.546191+00:00
-- url     : https://prove2.me/submissions/ea6d2c5f-ca0b-4dcf-ade4-7a565384d6fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every discount q≥ψ(θ) preserves the actual same-source
theta-exponential cash budget on the whole Stieltjes interval [0,T]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * q))
      ∂dividendMeasure D ω ∂P) ≤ 1 := by
  have hpoint (ω : Ω) (s : ℝ) :
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * q)) ≤
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      have hs : 0 ≤ (s.toNNReal : ℝ) := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) hs]
    · exact le_of_lt hθ
  calc
    _ ≤ (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
      ∂dividendMeasure D ω ∂P) :=
      lintegral_mono (fun ω => lintegral_mono (hpoint ω))
    _ ≤ 1 :=
      avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
        X D hD θ hθ T hT
