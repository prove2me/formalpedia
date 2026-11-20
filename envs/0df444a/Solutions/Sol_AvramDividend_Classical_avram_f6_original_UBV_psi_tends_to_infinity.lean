-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_psi_tends_to_infinity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:40:50.201025+00:00
-- url     : https://prove2.me/submissions/19c05a5a-8cd8-46d4-b91c-b638c51aba34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) :
    Tendsto X.ψ atTop atTop := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation
      X hBV 1 (by norm_num)
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop
      (φ + max 0 ((b - 1) * φ) + 1)] with x hx
  have hθ : 0 < x - φ := by
    have hm := le_max_left (0 : ℝ) ((b - 1) * φ)
    linarith
  have hlow : (b - 1) * φ ≤ x - φ := by
    have hm := le_max_right (0 : ℝ) ((b - 1) * φ)
    linarith
  have hdiv : b - 1 ≤ (x - φ) / φ :=
    (le_div_iff₀ hφ).2 hlow
  have he := levy_psi_root_shifted_increment_lower
    X 1 φ (x - φ) (by norm_num) hφ hθ hroot
  have hh : X.ψ (φ + (x - φ)) = X.ψ x := by ring
  rw [hh] at he
  have hfrac : (1 / φ) * (x - φ) = (x - φ) / φ := by ring
  rw [hfrac] at he
  linarith
