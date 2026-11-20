-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_all
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:35:26.366533+00:00
-- url     : https://prove2.me/submissions/44d9153a-49cd-43df-a98d-eb5a665535b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (θ : ℝ) :
    ∃ p lam : ℝ, 0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by
  have hB : 0 ≤ max θ 0 := le_max_right θ 0
  have hψ := avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
    X (max θ 0) hB
  exact avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
    X hBV θ hψ
