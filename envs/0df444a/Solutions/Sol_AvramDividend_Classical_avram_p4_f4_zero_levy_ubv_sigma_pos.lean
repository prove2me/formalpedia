-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_zero_levy_ubv_sigma_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:50:10.779026+00:00
-- url     : https://prove2.me/submissions/c6cdc32d-17f1-4ad0-aab3-c29aac4bc0ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (hν : X.ν = 0) :
    0 < X.σ := by
  have hσne : X.σ ≠ 0 := by
    intro hσ
    apply hBV
    change X.σ = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤
    constructor
    · exact hσ
    · rw [hν]
      simp
  exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hσne)
