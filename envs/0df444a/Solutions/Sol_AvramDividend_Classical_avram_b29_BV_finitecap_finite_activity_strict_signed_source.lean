-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_BV_finitecap_finite_activity_strict_signed_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:17:42.900195+00:00
-- url     : https://prove2.me/submissions/5ee09dd4-70d3-40c7-9be9-9e165b7bf028
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_physical_prefix_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_b29_BV_finitecap_finite_activity_uniform_signed_cash_source
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hwpos : 0 < w x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∃ u : ℕ → ℝ,
      Monotone u ∧
      (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      ∃ R J Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => R n ω + J n ω) P ∧
          (∫ ω, R n ω + J n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
          atTop (𝓝 (0 : ℝ)) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
           else 0) ≤
            w x + (R n ω + J n ω) + max (Err n ω) 0) := by
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have hClock :
      Monotone u ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n ≤ T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) := by
    simpa [u] using
      (avram_bv_strict6_original_physical_prefix_cofinal_clock T hTpos)
  rcases hClock with ⟨hmono, hu, hbelow, hcover⟩
  have hlt : ∀ n, u n < T := by
    intro n
    dsimp [u]
    have hp : 0 < T / ((n : ℝ) + 2) := by positivity
    linarith
  obtain ⟨R, J, Err, hSigned, hErrInt, hErrMean, hPhysical⟩ :=
    avram_b29_BV_finitecap_finite_activity_uniform_signed_cash_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc hwpos D hD
      hw_nonneg hjump T hT hTpos hFinite hActivity
  refine ⟨u, hmono, hu, hlt, hcover,
    R, J, Err, hSigned, hErrInt, hErrMean, ?_⟩
  intro n
  filter_upwards [hPhysical n] with ω hω
  exact hω
