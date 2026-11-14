-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:48:53.555917+00:00
-- url     : https://prove2.me/submissions/172e1447-74c5-44e0-84b0-a062d277e45f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
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
      ∃ J B R : Ω → ℝ,
        Integrable J P ∧ Integrable B P ∧ Integrable R P ∧
        (∫ ω, J ω ∂P) = 0 ∧
        (∫ ω, B ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, 0 ≤ R ω) ∧
        (∫ ω, R ω ∂P) ≤ ε ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + (J ω + B ω) + R ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n ε hε
  obtain ⟨τ, hτ, hτBound, hτStop, hτRuin,
    W, Cash, Term, M, G, H, hW, hCash, hTerm,
    hTermI, hCashI, hMI, hGI, hHI, hMean,
    hGH, hUpper, hFdom⟩ :=
    avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump T hT hInfinite n
  let J : Ω → ℝ := M
  let B : Ω → ℝ := fun ω => G ω + H ω
  let R : Ω → ℝ := fun _ => 0
  have hBI : Integrable B P := hGI.add hHI
  have hRI : Integrable R P := integrable_zero _ _ _
  have hBmean : (∫ ω, B ω ∂P) ≤ 0 := by
    have h0 : (∫ ω, B ω ∂P) ≤
        (∫ ω, (0 : ℝ) ∂P) :=
      integral_mono_ae hBI (integrable_const _) hGH
    simpa only [integral_zero] using h0
  have hRnonneg : ∀ᵐ ω ∂P, 0 ≤ R ω :=
    Filter.Eventually.of_forall (fun ω => le_refl (0 : ℝ))
  have hRmean : (∫ ω, R ω ∂P) ≤ ε := by
    simpa [R] using (le_of_lt hε)
  have hFupper : ∀ᵐ ω ∂P,
      F n ω ≤ w x + (J ω + B ω) + R ω := by
    filter_upwards [hUpper, hFdom] with ω hU hD
    dsimp [J, B, R]
    linarith
  exact ⟨J, B, R, hMI, hBI, hRI, hMean, hBmean,
    hRnonneg, hRmean, hFupper⟩
