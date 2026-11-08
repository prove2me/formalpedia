-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_global_postpayment_value_horizon_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:52:51.36637+00:00
-- url     : https://prove2.me/submissions/b457c547-e030-4997-9ff6-7c0d518865e3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Global postpayment values remain bounded across original ruin and horizon contacts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        |w (x + X.X t ω - rightLimit D t ω)| ≤ K := by
  let H : ℝ := max (x + max ((T : ℝ) * X.drift) 0) 0
  have hsub : Icc (0 : ℝ) H ⊆ Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn w (Icc (0 : ℝ) H) := hw_cont.mono hsub
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K₀ 0, le_max_right _ _, ?_⟩
  filter_upwards
    [avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
      X hBV x D hD] with ω hInc
  intro t ht
  let y : ℝ := x + X.X t ω - rightLimit D t ω
  have hD0 : 0 ≤ rightLimit D 0 ω := by
    calc
      0 = D 0 ω := (hD.1 ω).symm
      _ ≤ rightLimit D 0 ω := dividendStrategy_le_rightLimit D hD ω 0
  have hTime : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hStep : (t : ℝ) * X.drift ≤ max ((T : ℝ) * X.drift) 0 := by
    by_cases hd : 0 ≤ X.drift
    · exact (mul_le_mul_of_nonneg_right hTime hd).trans (le_max_left _ _)
    · have hdneg : X.drift ≤ 0 := le_of_not_ge hd
      have ht0 : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
      exact (mul_nonpos_of_nonneg_of_nonpos ht0 hdneg).trans
        (le_max_right _ _)
  have hInc0 := hInc 0 t (show (0 : ℝ≥0) ≤ t from zero_le)
  rw [X.X_zero ω] at hInc0
  norm_num at hInc0
  have hstepY : y ≤ x + (t : ℝ) * X.drift := by
    dsimp [y]
    linarith
  have hStepPlus : x + (t : ℝ) * X.drift ≤
      x + max ((T : ℝ) * X.drift) 0 := by
    simpa only [add_comm] using (add_le_add_left hStep x)
  have hyupper : y ≤ H := (hstepY.trans hStepPlus).trans (le_max_left _ _)
  change |w y| ≤ max K₀ 0
  by_cases hy : 0 ≤ y
  · have hb : ‖w y‖ ≤ K₀ := hK₀ y ⟨hy, hyupper⟩
    have habs : |w y| ≤ K₀ := by simpa only [Real.norm_eq_abs] using hb
    exact habs.trans (le_max_left _ _)
  · have hzero : w y = 0 := hw_neg y (lt_of_not_ge hy)
    simpa only [hzero, abs_zero] using (le_max_right K₀ 0)
