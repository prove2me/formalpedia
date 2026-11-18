-- Prove2me | solution 4 for AvramDividend.Classical.avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:22:02.125503+00:00
-- url     : https://prove2.me/submissions/b076f04d-31a8-44f7-bcfd-0057928b87a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
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
      ∃ M : Ω → ℝ, Integrable (F n) P ∧ Integrable M P ∧
        (∫ ω, M ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + M ω + ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hint := avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
    X hBV x C D hD w hw_cont hw_neg q hq T hT
  have hmono := avram_bvb60_original_all_BV_strict_cash_full_T_expected_monotone
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc D hD hw_nonneg hjump T hT
  have hfuture := avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite
  intro δ S F n ε hε
  have hAt : ∀ᶠ m : ℕ in atTop, n ≤ m := Filter.eventually_ge_atTop n
  obtain ⟨m, hnm, hmle⟩ := (hAt.and (hfuture ε hε)).exists
  have hMean : (∫ ω, F n ω ∂P) ≤ w x + ε :=
    (hmono n m hnm).trans hmle
  let b : ℝ := ∫ ω, F n ω ∂P
  let M : Ω → ℝ := fun ω => F n ω - b
  refine ⟨M, hint n, (hint n).sub (integrable_const b), ?_, ?_⟩
  · have hZero : (∫ ω, M ω ∂P) = 0 := by
      change (∫ ω, F n ω - b ∂P) = 0
      rw [integral_sub (hint n) (integrable_const b)]
      simp [b]
      exact sub_self _
    exact le_of_eq hZero
  · filter_upwards [] with ω
    dsimp [M, b]
    linarith
