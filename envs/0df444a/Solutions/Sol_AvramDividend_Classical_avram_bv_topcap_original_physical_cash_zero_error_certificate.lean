-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_topcap_original_physical_cash_zero_error_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:41:53.718021+00:00
-- url     : https://prove2.me/submissions/4aee02ff-57b5-40fd-a177-6151139540ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_top_cap_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Top-cap actual stopped physical F_n: BVB62 gives integrability,
   Redux6 gives the exact all-n expectation budget, the elementary
   signed-zero-error certificate closes the physical mesh conclusion. -/

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
    (T : ℝ) (hT : 0 < T) (hTop : C = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∃ M B Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hFI : ∀ n, Integrable (F n) P := by
    simpa only [F, δ, S] using
      (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT)
  obtain ⟨hδposAll, hδleAll, _, _⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hT
  have hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
    intro n
    have hδpos : 0 < δ n := by
      simpa only [δ] using hδposAll n
    have hδle : δ n ≤ T := by
      simpa only [δ] using hδleAll n
    have hs0 : 0 ≤ T - δ n := sub_nonneg.mpr hδle
    have hsT : T - δ n < T := sub_lt_self T hδpos
    have hSource :=
      avram_redux6_bv_single_clock_top_cap_expected_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        T hT.le hT hTop (T - δ n) hs0 hsT
    simpa only [F, δ, S] using hSource
  let B : ℕ → Ω → ℝ := fun n ω => F n ω - w x
  have hBI : ∀ n, Integrable (B n) P := by
    intro n
    exact (hFI n).sub (integrable_const _)
  have hBmean : ∀ n, (∫ ω, B n ω ∂P) ≤ 0 := by
    intro n
    have hEq : (∫ ω, F n ω - w x ∂P) =
        (∫ ω, F n ω ∂P) - w x := by
      rw [integral_sub (hFI n) (integrable_const _)]
      simp
    change (∫ ω, F n ω - w x ∂P) ≤ 0
    rw [hEq]
    exact sub_nonpos.mpr (hMean n)
  change ∃ M B' Err : ℕ → Ω → ℝ,
    (∀ n, Integrable (fun ω => M n ω + B' n ω) P ∧
      (∫ ω, M n ω + B' n ω ∂P) ≤ 0) ∧
    (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
    Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
    (∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n ω + B' n ω) + max (Err n ω) 0)
  refine ⟨(fun _ _ => 0), B, (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · simpa only [zero_add] using hBI n
    · simpa only [zero_add] using hBmean n
  · intro n
    simp
  · simp
  · intro n
    filter_upwards [] with ω
    change F n ω ≤ w x + (0 + B n ω) + max (0 : ℝ) 0
    dsimp [B]
    simp
