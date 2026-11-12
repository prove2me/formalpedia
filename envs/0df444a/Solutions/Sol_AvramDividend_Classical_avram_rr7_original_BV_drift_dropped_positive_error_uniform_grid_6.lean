-- Prove2me | solution 6 for AvramDividend.Classical.avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:34:40.529435+00:00
-- url     : https://prove2.me/submissions/3cc87f4a-85f8-410c-9ffe-1711d17c92bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Centre an integrable original-grid nonpositive-mean certificate. -/
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
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∃ M Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤
        w x + M n ω + max (Err n ω) 0) := by
  intro δ S F
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨M, B, Err, hMB, hErrInt, hErrMean, hPhys⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hT
  let MC : ℕ → Ω → ℝ := fun n ω =>
    M n ω + B n ω - (∫ ω', M n ω' + B n ω' ∂P)
  refine ⟨MC, Err, ?_, hErrInt, hErrMean, ?_⟩
  · intro n
    have hi : Integrable (fun ω => M n ω + B n ω) P := (hMB n).1
    have hmc : Integrable (MC n) P := hi.sub (integrable_const _)
    constructor
    · exact hmc
    · change (∫ ω, M n ω + B n ω -
        (∫ ω', M n ω' + B n ω' ∂P) ∂P) = 0
      rw [integral_sub hi (integrable_const _)]
      simp
  · intro n
    filter_upwards [hPhys n] with ω hω
    have hF : F n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
      simpa only [F, S, δ] using hω
    have hm : (∫ ω', M n ω' + B n ω' ∂P) ≤ 0 := (hMB n).2
    change F n ω ≤ w x + MC n ω + max (Err n ω) 0
    dsimp [MC]
    linarith
