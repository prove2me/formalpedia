-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite54_original_finitecap_gaussian_strip_gradient_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:30:42.824186+00:00
-- url     : https://prove2.me/submissions/4faa1787-549c-4ba8-98dd-cfd05259ac0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_original_C2_interior_differentiable
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
import Theorems.Thm_AvramDividend_Classical_avram_gfinite50_zerojump_cap_strip_gradient_uniform
import Theorems.Thm_AvramDividend_Classical_avram_gfinite53_original_interior_C2_derivative_certificates
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ Ico (C.toReal / 2) C.toReal, deriv w y ≤ B := by
  let c : ℝ := C.toReal
  let a : ℝ := c / 2
  have hc : 0 < c := ENNReal.toReal_pos (ne_of_gt hC) hFinite
  have ha : 0 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  have hCeq : ENNReal.ofReal c = C := ENNReal.ofReal_toReal hFinite
  have hInterior (y : ℝ) (hy : y ∈ Ico a c) :
      0 < y ∧ ENNReal.ofReal y < C := by
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    have hyC : ENNReal.ofReal y < C :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hFinite).2
        (by simpa [c] using hy.2)
    exact ⟨hy0, hyC⟩
  have hSmoothReal : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c} := by
    simpa [hCeq] using hw_smooth
  have hDiff : DifferentiableOn ℝ w (Ioo (0 : ℝ) c) :=
    avram_p4_e_localise_finitecap_original_C2_interior_differentiable
      w c hSmoothReal
  have hGradReal : ∀ y : ℝ, 0 < y → y < c → 1 ≤ deriv w y := by
    intro y hy0 hyc
    have hyC : ENNReal.ofReal y < C :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hFinite).2
        (by simpa [c] using hyc)
    exact hw_grad y hy0 hyC
  have hNonneg : ∀ y : ℝ, 0 ≤ y → y ≤ c → 0 ≤ w y :=
    avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
      w c (le_of_lt hc) hw0 hw_cont hDiff hGradReal
  have hσ : X.σ ≠ 0 :=
    ne_of_gt (avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded X hν hBV)
  have hBound := avram_gfinite50_zerojump_cap_strip_gradient_uniform
    X hν hσ q hq w a c hac
    (fun y hy => hNonneg y (le_trans (le_of_lt ha) hy.1) (le_of_lt hy.2))
    (fun y hy => le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (hw_grad y (hInterior y hy).1 (hInterior y hy).2))
    (fun y hy => (hw_gen y (hInterior y hy).1 (hInterior y hy).2).2)
    (fun y hy =>
      (avram_gfinite53_original_interior_C2_derivative_certificates
        w C hw_smooth y (hInterior y hy).1 (hInterior y hy).2).1)
    (fun y hy =>
      (avram_gfinite53_original_interior_C2_derivative_certificates
        w C hw_smooth y (hInterior y hy).1 (hInterior y hy).2).2)
  simpa [a, c] using hBound
