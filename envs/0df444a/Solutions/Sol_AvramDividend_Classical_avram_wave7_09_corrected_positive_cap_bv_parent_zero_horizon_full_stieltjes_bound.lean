-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:53:43.110603+00:00
-- url     : https://prove2.me/submissions/04d382fb-ace8-433a-bdc7-4f1e35045cf2

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

/-- The exact corrected positive-cap BV parent holds at T=0 from the
chronological right atom, admissible post-payment reserve and gradient secant,
with no import of any open global stochastic HJB core. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
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
