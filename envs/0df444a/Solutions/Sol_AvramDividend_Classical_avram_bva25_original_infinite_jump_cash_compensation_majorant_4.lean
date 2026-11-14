-- Prove2me | solution 4 for AvramDividend.Classical.avram_bva25_original_infinite_jump_cash_compensation_majorant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:14:39.226562+00:00
-- url     : https://prove2.me/submissions/2803bd9b-1132-41d3-b79b-ea84425636fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva35_original_BV_strict_inner_cash_terminal_monotone
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
    ∀ n : ℕ, ∃ M : Ω → ℝ,
      Integrable (F n) P ∧ Integrable M P ∧
      (∫ ω, M ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, F n ω ≤ w x + M ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n
  have hI := avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hInfinite
  have hMon := avram_bva35_original_BV_strict_inner_cash_terminal_monotone
    X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hInfinite
  have hBudget := avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hInfinite
  have hUpper (ε : ℝ) (hε : 0 < ε) :
      (∫ ω, F n ω ∂P) ≤ w x + ε := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hBudget ε hε)
    let m : ℕ := max n N
    have hPoint : ∀ᵐ ω ∂P, F n ω ≤ F m ω :=
      Filter.Eventually.of_forall
        (fun ω => hMon n m (Nat.le_max_left n N) ω)
    have hInt : (∫ ω, F n ω ∂P) ≤ (∫ ω, F m ω ∂P) :=
      integral_mono_ae (hI n) (hI m) hPoint
    exact hInt.trans (hN m (Nat.le_max_right n N))
  have hMean : (∫ ω, F n ω ∂P) ≤ w x := by
    by_contra hBad
    have hlt : w x < (∫ ω, F n ω ∂P) := lt_of_not_ge hBad
    let ε : ℝ := ((∫ ω, F n ω ∂P) - w x) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hNear := hUpper ε hε
    dsimp [ε] at hNear
    linarith
  let M : Ω → ℝ := fun ω => F n ω - w x
  have hMI : Integrable M P := (hI n).sub (integrable_const _)
  refine ⟨M, hI n, hMI, ?_, ?_⟩
  · have hMeanM : (∫ ω, M ω ∂P) = (∫ ω, F n ω ∂P) - w x := by
      change (∫ ω, F n ω - w x ∂P) =
        (∫ ω, F n ω ∂P) - w x
      rw [integral_sub (hI n) (integrable_const _)]
      simp <;> ring
    linarith
  · filter_upwards [] with ω
    dsimp [M]
    linarith
