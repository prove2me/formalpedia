-- Prove2me | solution 8 for AvramDividend.Classical.avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:25:53.083979+00:00
-- url     : https://prove2.me/submissions/36471ea8-4acd-42cd-9dc5-8ac4ce9cbe9f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_compensated_error_without_meas
import Mathlib.Tactic.GCongr
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
  obtain ⟨B, hB, hBsign, _⟩ :=
    avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
      X hX hBV q w C hw_gen x D hD.1.1 T hT u
      (by
        intro n i
        have hReal : (u n i : ℝ) ≤ (u n (i + 1) : ℝ) := by
          rw [huniform n i, huniform n (i + 1)]
          gcongr
          exact_mod_cast Nat.le_succ i
        exact_mod_cast hReal) huniform
  obtain ⟨M, Err, hMI, hEI, hErr, hBudget⟩ :=
    avram_a19_nonint_original_compensated_error_without_meas
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  intro δ S F
  refine ⟨M, Err, hMI, hEI, hErr, ?_⟩
  intro n
  filter_upwards [hBudget n, hBsign] with ω hω hsign
  have hBn : B n ω ≤ 0 := hsign n
  change F n ω ≤ w x + M n ω + max (Err n ω) 0
  linarith
