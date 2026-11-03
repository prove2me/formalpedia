-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_positive_cap_bv_zero_horizon_analytic_minimal_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:47:51.974218+00:00
-- url     : https://prove2.me/submissions/5101fcd5-d28c-4649-a60f-dcfbca54dc77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At the exact zero horizon the original positive-cap BV Stieltjes
bound requires neither Standing, q>0, generator HJB, zero-negative
boundary, nor the open positive-time nonnegative-value premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hSplit :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun hn => False.elim (hn hBV), fun _ => hw_smooth⟩
  have hAtom :=
    avram_wave5_03_original_separate_gradient_right_atom_control
      X w C hC hw_cont hSplit hw_grad x hxc D hD
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hjump : ∀ ω,
      rightLimit D 0 ω - D 0 ω ≤
        w x - w (x - (rightLimit D 0 ω - D 0 ω)) := by
    intro ω
    have hz : D 0 ω = 0 := hs.1 ω
    have hXz : X.X 0 ω = 0 := X.X_zero ω
    have h := hAtom ω 0 (Or.inl rfl)
    simpa [riskProcess, hz, hXz] using h
  have hpost : ∀ ω,
      0 ≤ w (x - (rightLimit D 0 ω - D 0 ω)) := by
    intro ω
    obtain ⟨hnonneg, hcap⟩ :=
      capped_postPaymentReserve_initial_state X x C D hD hxc ω
    have hsec :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad 0
        (x + X.X 0 ω - rightLimit D 0 ω)
        (le_refl (0 : ℝ)) hnonneg hcap
    have hw : 0 ≤ w (x + X.X 0 ω - rightLimit D 0 ω) := by
      linarith
    have hz : D 0 ω = 0 := hs.1 ω
    have hXz : X.X 0 ω = 0 := X.X_zero ω
    simpa [hz, hXz] using hw
  exact truncated_zero_horizon_bound_of_initial_jump_secant
    X q x w D hs hjump hpost
