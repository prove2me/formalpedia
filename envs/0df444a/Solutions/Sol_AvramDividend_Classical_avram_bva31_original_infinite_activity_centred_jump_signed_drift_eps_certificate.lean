-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva31_original_infinite_activity_centred_jump_signed_drift_eps_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:57:16.873204+00:00
-- url     : https://prove2.me/submissions/2b266d3b-2569-49b9-9666-6fde2b21377a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva32_original_infinite_activity_integrable_positive_grid_error_certificate
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ J B : Ω → ℝ,
        Integrable (F n) P ∧ Integrable J P ∧ Integrable B P ∧
        (∫ ω, J ω ∂P) = 0 ∧
        (∫ ω, B ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + (J ω + B ω) + ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n ε hε
  obtain ⟨J, B, R, hF, hJ, hB, hR, hJmean, hBmean, hRpos, hRmean, hPath⟩ :=
    avram_bva32_original_infinite_activity_integrable_positive_grid_error_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite n ε hε
  let μR : ℝ := ∫ ω, R ω ∂P
  have hCentre : (∫ ω, J ω + R ω - μR ∂P) = 0 := by
    change (∫ ω, ((J + R) - fun _ : Ω => μR) ω ∂P) = 0
    rw [integral_sub' (hJ.add hR) (integrable_const μR)]
    rw [integral_add' hJ hR]
    simp [μR, hJmean]
  refine ⟨fun ω => J ω + R ω - μR, B, hF,
    (hJ.add hR).sub (integrable_const μR), hB, hCentre, hBmean, ?_⟩
  filter_upwards [hPath] with ω hp
  have hm : μR ≤ ε := hRmean
  linarith
