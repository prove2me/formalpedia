-- Prove2me | solution 11 for AvramDividend.Classical.avram_integration_p3_original_strict_source_residual_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:33:11.380209+00:00
-- url     : https://prove2.me/submissions/3a5c34d0-5364-44f2-b708-722fa28d4275
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_physical_prefix_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An acyclic original-process residual witness derived from the physical
positive-error grid source, allowing a nonintegrable negative generator. -/
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + E ω) := by
  classical
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) := by
    intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
          T - T / ((n : ℝ) + 2)
      push_cast
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  have hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1) := by
    intro n i _
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    have hi : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ i
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi (le_of_lt hTpos)) (by positivity)
  have huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2) := by
    intro n i
    rfl
  obtain ⟨M, Err, hM, hErrInt, hErrMean, hF⟩ :=
    avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
      u hgrid hmono huniform
  let S : ℝ≥0 := ⟨T, hT⟩
  let v : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  obtain ⟨hvmono, hvnonneg, hvbelow, hvcover⟩ :=
    avram_bv_strict6_original_physical_prefix_cofinal_clock T hTpos
  let B : ℕ → Ω → ℝ := fun _ _ => 0
  have hMbudget : ∀ n, Integrable (M n) P ∧
      (∫ ω, M n ω ∂P) ≤ 0 := by
    intro n
    exact ⟨(hM n).1, le_of_eq (hM n).2⟩
  have hBbudget : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    exact Filter.Eventually.of_forall (fun ω => by simp [B])
  have hPhysical : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    filter_upwards [hF n] with ω hω
    have hST : (S : ℝ) = T := rfl
    rw [hST]
    have hS : S = (⟨T, le_of_lt hTpos⟩ : ℝ≥0) := by
      apply Subtype.ext
      rfl
    rw [hS]
    simpa only [v, B, add_zero] using hω
  have hMean :=
    avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      S v hvmono hvnonneg hvbelow hvcover M B Err
      hMbudget hBbudget hErrInt hErrMean hPhysical
  exact avram_p3_bv_original_source_witness_from_strict_mean
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT hMean
