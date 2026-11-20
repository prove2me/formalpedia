-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:22:40.752175+00:00
-- url     : https://prove2.me/submissions/ec61799f-9ab2-44b5-8a64-c969d11a7022

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_all
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_runningSup_exp_L1
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) (n : ℝ≥0) :
    Integrable (fun ω : Ω => Real.exp (θ * runningSup X n ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨p, lam, hp, hlam, hθlam, hroot⟩ :=
    avram_f6_original_UBV_psi_root_above_theta_all X hBV θ
  exact avram_f6_original_positive_psi_root_runningSup_exp_L1
    X p lam θ hp hlam hroot hθ hθlam n
