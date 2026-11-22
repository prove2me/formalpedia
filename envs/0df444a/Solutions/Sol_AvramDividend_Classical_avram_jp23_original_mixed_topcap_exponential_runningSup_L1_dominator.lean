-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:43:11.350025+00:00
-- url     : https://prove2.me/submissions/e314f6a9-07c7-4238-a3ba-cf243413fa0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (n : ℝ≥0) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      (∀ y : ℝ, 0 ≤ y →
        w y ≤ K * Real.exp (θ * y)) ∧
      Integrable (fun ω : Ω =>
        K * Real.exp (θ * (x + runningSup X n ω))) P := by
  have hνFin : X.ν (Iio (0 : ℝ)) < ⊤ :=
    lt_top_iff_ne_top.mpr hFiniteActivity
  obtain ⟨θ, K, hθ, hK, hwGrowth⟩ :=
    avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
      X hX hBV hνFin q hq w C hC hTop hw0 hw_cont
      hw_neg hw_smooth hw_gen hw_grad
  refine ⟨θ, K, hθ, hK, hwGrowth, ?_⟩
  have hSupI :
      Integrable (fun ω : Ω =>
        Real.exp (θ * runningSup X n ω)) P :=
    avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
      X hBV θ hθ n
  have hScaled :
      Integrable (fun ω : Ω =>
        (K * Real.exp (θ * x)) *
          Real.exp (θ * runningSup X n ω)) P :=
    hSupI.const_mul (K * Real.exp (θ * x))
  have hEq :
      (fun ω : Ω => K * Real.exp (θ * (x + runningSup X n ω))) =
      (fun ω : Ω => (K * Real.exp (θ * x)) *
        Real.exp (θ * runningSup X n ω)) := by
    funext ω
    rw [mul_add, Real.exp_add, mul_assoc]
  rw [hEq]
  exact hScaled
