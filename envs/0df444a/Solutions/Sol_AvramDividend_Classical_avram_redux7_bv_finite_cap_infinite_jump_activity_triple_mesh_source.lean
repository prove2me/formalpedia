-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux7_bv_finite_cap_infinite_jump_activity_triple_mesh_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:30:53.05264+00:00
-- url     : https://prove2.me/submissions/2aa1ea18-2839-4450-9599-524a8d393927
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_integrable_expected_budget_to_triple_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_finite_cap_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_fatou_real_grid_certificate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV finite-activity mesh certificate follows from the
physical strict-prefix expected budget and source-exact Fatou convergence. -/
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    let Y : Ω → ℝ := fun ω =>
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0)
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M B DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ w x + Mmesh n ω + Bmesh n ω) := by
  classical
  intro Y
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  obtain ⟨hδpos, hδle, hδanti, hδ⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  let S : ℝ≥0 := ⟨T, hT⟩
  let term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      term ω
  obtain ⟨hF, hFatou⟩ :=
    avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      T hTpos hw_nonneg δ hδpos hδle hδanti hδ
  have hExpected : ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
    intro n
    have hs0 : 0 ≤ T - δ n := sub_nonneg.mpr (hδle n)
    have hsT : T - δ n < T := sub_lt_self T (hδpos n)
    exact avram_redux6_bv_single_clock_finite_cap_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT hTpos hFinite (T - δ n) hs0 hsT
  have hYPair :=
    avram_p3_bv_original_strict_reward_L1_nonnegative
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      T hT hTpos hw_nonneg
  have hYInt : Integrable Y P := hYPair.1
  have hYNonneg : ∀ ω, 0 ≤ Y ω := hYPair.2
  have hwx : 0 ≤ w x := by
    have hz : 0 ≤ (∫ ω, F 0 ω ∂P) :=
      integral_nonneg (hF 0).2.2
    exact hz.trans (hExpected 0)
  let Fe : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (F n ω)
  have hFeMeas : ∀ n, Measurable (Fe n) := by
    intro n
    exact ENNReal.measurable_ofReal.comp (hF n).1
  have hFeMean : ∀ n, (∫⁻ ω, Fe n ω ∂P) ≤ ENNReal.ofReal (w x) := by
    intro n
    change (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal (w x)
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n).2.1
      (Filter.Eventually.of_forall (hF n).2.2)]
    exact ENNReal.ofReal_le_ofReal (hExpected n)
  have hFatouAe : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
      liminf (fun n => Fe n ω) atTop :=
    Filter.Eventually.of_forall hFatou
  have hYEnn : (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
    exact avram_limit2_original_signed_strict_fatou_real_grid_certificate
      X q x T D term Fe (ENNReal.ofReal (w x))
      hFeMeas hFeMean hFatouAe
  have hBudget : (∫ ω, Y ω ∂P) ≤ w x := by
    have hOfReal : ENNReal.ofReal (∫ ω, Y ω ∂P) ≤
        ENNReal.ofReal (w x) := by
      rwa [ofReal_integral_eq_lintegral_ofReal hYInt
        (Filter.Eventually.of_forall hYNonneg)]
    have hz : 0 ≤ (∫ ω, Y ω ∂P) := integral_nonneg hYNonneg
    have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hOfReal
    simpa only [ENNReal.toReal_ofReal hz, ENNReal.toReal_ofReal hwx] using hReal
  exact avram_sweep16_integrable_expected_budget_to_triple_mesh
    Y (w x) hYInt hBudget
