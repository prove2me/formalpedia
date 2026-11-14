-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_topcap_centred_cash_infinite_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:49:10.875994+00:00
-- url     : https://prove2.me/submissions/9b4f9906-f603-4218-9a9a-047a7e12f4a0

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_a19_single_strict_clock_top_cap_HJB_source
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (hTop : C = ⊤)
    (hActivity : ¬ (X.ν (Iio (0 : ℝ)) < ⊤)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n)  := by
  classical
  intro δ S F
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hT
  have hProperties := avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
    X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
    hw_nonneg δ hδpos hδle hδanti hδlim
  have hL1 (n : ℕ) : Integrable (F n) P := (hProperties.1 n).2.1
  have hBudget (n : ℕ) : (∫ ω, F n ω ∂P) ≤ w x := by
    exact avram_a19_single_strict_clock_top_cap_HJB_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T (le_of_lt hT) hT hTop
      (T - δ n) (sub_nonneg.mpr (hδle n)) (sub_lt_self T (hδpos n))
  refine ⟨(fun n ω => F n ω - (∫ v, F n v ∂P)),
    (fun _ _ => 0), (fun n => 1 / ((n : ℝ) + 1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    constructor
    · exact (hL1 n).sub (integrable_const _)
    · rw [integral_sub (hL1 n) (integrable_const _)]
      simp
  · intro n
    simpa only [max_self] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · intro n
    filter_upwards [] with ω
    simp only [max_self, add_zero]
    linarith [hBudget n]
  · intro n
    simp only [max_self, integral_zero]
    positivity
