-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:33:02.10674+00:00
-- url     : https://prove2.me/submissions/91d713e9-854d-4c6f-a163-6f9d19248b21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
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
    ∃ N : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable
        (fun ω => max (F m ω - (w x + N m ω)) 0) P) ∧
      Tendsto (fun m =>
        ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F
  obtain ⟨N, hN, hLimit⟩ :=
    avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  have hZero : ∀ m : ℕ, Integrable (fun _ : Ω => (0 : ℝ)) P := by
    intro m
    exact integrable_const 0
  have hIntN : ∀ m, Integrable (N m) P := fun m => (hN m).1
  have hExcess : ∀ m, Integrable
      (fun ω => max (F m ω - (w x + N m ω)) 0) P := by
    intro m
    have hh :=
      avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
        X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
        (fun _ _ => 0) N hZero hIntN m
    simpa only [zero_add] using hh
  exact ⟨N, hN, hExcess, hLimit⟩
