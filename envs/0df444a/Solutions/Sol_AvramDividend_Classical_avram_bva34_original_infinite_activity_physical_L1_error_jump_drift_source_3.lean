-- Prove2me | solution 3 for AvramDividend.Classical.avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:03:27.51226+00:00
-- url     : https://prove2.me/submissions/2f69f3f6-b38a-4e60-8d39-01a158a23058
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
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
  have hI (m : ℕ) : Integrable (F m) P :=
    avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite m
  have hMon : ∀ᵐ ω ∂P, ∀ i k : ℕ, i ≤ k → F i ω ≤ F k ω :=
    avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
      X x C D hD w q T hT
  have hTail : ∀ᶠ m in (atTop : Filter ℕ),
      (∫ ω, F m ω ∂P) ≤ w x + ε :=
    avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hTail
  let k : ℕ := max n N
  have hCompare : ∀ᵐ ω ∂P, F n ω ≤ F k ω := by
    filter_upwards [hMon] with ω hω
    exact hω n k (le_max_left n N)
  have hAvg : (∫ ω, F n ω ∂P) ≤ w x + ε :=
    (integral_mono_ae (hI n) (hI k) hCompare).trans
      (hN k (le_max_right n N))
  let avg : ℝ := ∫ ω, F n ω ∂P
  let J : Ω → ℝ := fun ω => F n ω - avg
  let B : Ω → ℝ := fun _ => 0
  let R : Ω → ℝ := fun _ => ε
  have hJI : Integrable J P := (hI n).sub (integrable_const avg)
  have hBI : Integrable B P := integrable_zero _ _ _
  have hRI : Integrable R P := integrable_const ε
  have hJmean : (∫ ω, J ω ∂P) = 0 := by
    change (∫ ω, F n ω - avg ∂P) = 0
    rw [integral_sub (hI n) (integrable_const avg)]
    simp [avg]
  have hBmean : (∫ ω, B ω ∂P) ≤ 0 := by simp [B]
  have hRpos : ∀ᵐ ω ∂P, 0 ≤ R ω :=
    Filter.Eventually.of_forall (fun _ => by simpa [R] using le_of_lt hε)
  have hRmean : (∫ ω, R ω ∂P) ≤ ε := by simp [R]
  have hDom : ∀ᵐ ω ∂P,
      F n ω ≤ w x + (J ω + B ω) + R ω := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [J, B, R, avg]
    linarith
  exact ⟨J, B, R, hJI, hBI, hRI,
    hJmean, hBmean, hRpos, hRmean, hDom⟩
