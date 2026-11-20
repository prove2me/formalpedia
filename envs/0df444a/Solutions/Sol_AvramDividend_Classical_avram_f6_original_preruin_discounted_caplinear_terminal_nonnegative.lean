-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_preruin_discounted_caplinear_terminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:40:44.51958+00:00
-- url     : https://prove2.me/submissions/f594aa34-7c13-45cd-8dc6-3998597140e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_allcap_original_caplinear_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ Real.exp (-(q * (t : ℝ))) *
      (let y := x + X.X t ω - rightLimit D t ω
       if ENNReal.ofReal y ≤ C then w y
       else w C.toReal + (y - C.toReal)) := by
  have hpoint : (t : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) :=
    ⟨by exact_mod_cast t.property, le_rfl⟩
  have hsolv : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    simpa using
      (avram_wave5_04b_closed_preruin_actual_postpayment_solvency
        X x C D hD ω t ht (t : ℝ) hpoint)
  have hdiff : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hval := avram_f6_allcap_original_caplinear_value_nonnegative
    C hC w hw0 hw_cont hdiff hw_grad
    (x + X.X t ω - rightLimit D t ω) hsolv
  exact mul_nonneg (Real.exp_nonneg _) hval
