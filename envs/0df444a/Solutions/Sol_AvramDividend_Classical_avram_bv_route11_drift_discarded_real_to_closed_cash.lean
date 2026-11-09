-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_route11_drift_discarded_real_to_closed_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T11:55:32.781857+00:00
-- url     : https://prove2.me/submissions/55980310-df3d-4414-bea8-d30632190216

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A generator-discarded real stopped budget controls the closed Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hDiscard :
      let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
      let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
      ∃ (M Err : ℕ → Ω → ℝ),
        (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
            (if (S : ℝ≥0∞) < ruinTime X x D ω then
              Real.exp (-(q * T)) * w (riskProcess X x D S ω)
            else 0) ≤
          w x + M n ω + max (Err n ω) 0)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  dsimp only at hDiscard
  obtain ⟨M, Err, hM, hErrInt, hErrMean, hPhysical⟩ := hDiscard
  let v : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hv := avram_p3_grid4_strict_physical_endpoint_cofinal_for_signed_fatou T hT
  change Monotone v ∧ (∀ n, 0 ≤ v n) ∧ (∀ n, v n ≤ T) ∧
    (∀ s : ℝ, s < T → ∃ n, s < v n) at hv
  obtain ⟨hvMono, hvZero, hvTop, hvCover⟩ := hv
  let B : ℕ → Ω → ℝ := fun _ _ => 0
  have hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    filter_upwards [] with ω
    exact le_refl 0
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
    apply hCore hM hB hErrInt hErrMean
    intro n
    filter_upwards [hPhysical n] with ω hω
    by_cases hAlive : (S : ℝ≥0∞) < ruinTime X x D ω
    · convert hω using 1 <;> simp [S, v, B, hAlive, add_assoc] <;>
        exact Or.inl (Or.inl rfl)
    · convert hω using 1 <;> simp [S, v, B, hAlive, add_assoc] <;>
        exact Or.inl (Or.inl rfl)
  exact avram_bv_env3_original_strict_expected_to_full_atom_ennreal
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hjump T (le_of_lt hT) hT hStrict
