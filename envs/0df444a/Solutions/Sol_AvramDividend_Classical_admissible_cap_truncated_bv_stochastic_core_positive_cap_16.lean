-- Prove2me | solution 16 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:55:40.636197+00:00
-- url     : https://prove2.me/submissions/7fc7d45e-04fe-4b71-a008-6f336be8d05a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Reduce the positive-cap BV core to a source-exact, drift-discarded grid. -/
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
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    exact
      avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hxc D hD hw_nonneg
  · obtain ⟨u, hgrid, hmono, huniform⟩ :=
      avram_a19_physical_strict_horizon_uniform_grid T hpos
    let S : ℝ≥0 := ⟨T, le_of_lt hpos⟩
    have hSource :=
      avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hpos u
        hgrid hmono huniform
    dsimp only at hSource
    obtain ⟨M, Err, hM, hErrInt, hErrMean, hPhysical⟩ := hSource
    let v : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
    have hv := avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou T hpos
    change Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < v n) at hv
    obtain ⟨hvMono, hvZero, hvTop, hvCover⟩ := hv
    let B : ℕ → Ω → ℝ := fun _ _ => 0
    have hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
      intro n
      filter_upwards [] with ω
      exact le_refl 0
    have hMNonpos : ∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) ≤ 0 := by
      intro n
      exact ⟨(hM n).1, le_of_eq (hM n).2⟩
    have hStrict :
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) *
              w (riskProcess X x D S ω)
          else 0) ∂P) ≤ w x := by
      have hCore :=
        avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
          X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
          S v hvMono hvZero hvTop hvCover
          M B Err
      apply hCore hMNonpos hB hErrInt hErrMean
      intro n
      filter_upwards [hPhysical n] with ω hω
      by_cases hAlive : (S : ℝ≥0∞) < ruinTime X x D ω
      · convert hω using 1 <;> simp [S, v, B, hAlive, add_assoc] <;>
          exact Or.inl (Or.inl rfl)
      · convert hω using 1 <;> simp [S, v, B, hAlive, add_assoc] <;>
          exact Or.inl (Or.inl rfl)
    exact avram_bv_env3_original_strict_expected_to_full_atom_ennreal
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD hjump T hT hpos hStrict
