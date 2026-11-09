-- Prove2me | solution 4 for AvramDividend.Classical.avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:53:20.935429+00:00
-- url     : https://prove2.me/submissions/002849cf-f354-42a5-b630-f03ce6d7fcdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_single_signed_strict_source_bridge
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
import Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_prefix_mono_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A full strict signed budget bounds every shorter physical uniform prefix. -/
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
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Z, hZI, hZMean, hStrict⟩ :=
    avram_p3_grid4_original_single_signed_strict_source_bridge
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T (le_of_lt hT) hT
  dsimp only
  refine ⟨(fun _ ω => Z ω - ∫ ω', Z ω' ∂P), (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · exact hZI.sub (integrable_const _)
    · rw [integral_sub hZI (integrable_const _)]
      simp
  · intro n
    simpa using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · intro n
    filter_upwards [hStrict] with ω hω
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    have hClosedIntegrable : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic T)
        (dividendMeasure D ω) :=
      avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
        D hD.1.1 ω (ruinTime X x D ω) ⟨T, le_of_lt hT⟩ q (le_of_lt hq)
    have hExpNN : 0 ≤ᵐ[(dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic T)]
        (fun t : ℝ => Real.exp (-(q * t))) :=
      Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
    have hClosedEq := ofReal_integral_eq_lintegral_ofReal hClosedIntegrable hExpNN
    have hClosedFinite :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
      rw [← hClosedEq]
      exact ENNReal.ofReal_lt_top
    have hSubset : paymentTimes (ruinTime X x D ω) ∩ Iio T ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by
      intro t ht
      exact ⟨ht.1, Set.mem_Iic.mpr ((Set.mem_Iio.mp ht.2).le)⟩
    have hStrictFinite :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
      have hle :
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
        lintegral_mono_set hSubset
      exact (lt_of_le_of_lt hle hClosedFinite).ne
    have hEndpoint : T - T / ((n : ℝ) + 2) ≤ T := by
      have hn : (0 : ℝ) ≤ T / ((n : ℝ) + 2) := by positivity
      linarith
    have hCash := avram_a19_discounted_cash_prefix_mono_finite
      D ω (ruinTime X x D ω) q
      (T - T / ((n : ℝ) + 2)) T hEndpoint hStrictFinite
    have hBound :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (T - T / ((n : ℝ) + 2)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + Z ω := by
      exact le_trans (add_le_add_left hCash _) hω
    simpa using (le_trans hBound (by simp only [max_self, add_zero]; linarith [hZMean] :
      w x + Z ω ≤ w x + (Z ω - ∫ ω', Z ω' ∂P) + max (0 : ℝ) 0))
