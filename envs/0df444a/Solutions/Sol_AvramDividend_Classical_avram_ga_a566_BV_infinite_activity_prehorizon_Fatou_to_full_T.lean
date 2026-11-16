-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a566_BV_infinite_activity_prehorizon_Fatou_to_full_T
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:16:06.468067+00:00
-- url     : https://prove2.me/submissions/067c4a2f-01cc-4eb9-94b4-7c40a3b84895

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a568_BV_true_strict_terminal_reward_measurable_nonnegative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a565_two_stage_Fatou_expected_budget_bridge
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_positive_initial_value_of_positive_reserve
import Theorems.Thm_AvramDividend_Classical_avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hactivity : ¬ X.ν (Iio (0 : ℝ)) < ⊤)
    (hPre : ∀ (r : ℝ≥0), 0 < r → (r : ℝ) < T →
      (∫⁻ ω, ENNReal.ofReal
        ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
         (if (r : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
          else 0)) ∂P) ≤ ENNReal.ofReal (w x)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by
  classical
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, hT⟩
  let r : ℕ → ℝ≥0 := fun n => Real.toNNReal (T - δ n)
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  let G : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (r n : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨hδpos, _, hδanti, hδlim⟩ :=
    avram_a19_uniform_delta_profile T hTpos
  have hFI : ∀ n, Integrable (F n) P :=
    avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hTpos
  have hK : 0 ≤ w x := by
    rcases eq_or_lt_of_le hx with h0 | hpos
    · simpa [h0] using hw0
    · exact (avram_p3_grid4_positive_initial_value_of_positive_reserve
        C hC w hw_cont hw0 hw_smooth hw_grad x hpos hxc).le
  obtain ⟨hYnn, hYm⟩ :=
    avram_ga_a568_BV_true_strict_terminal_reward_measurable_nonnegative
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
      hFinite hactivity
  obtain ⟨hGm, hFnear⟩ :=
    avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos hactivity
  have hYnear : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop :=
    Filter.Eventually.of_forall (fun ω : Ω => by
      simpa only [Y, F, δ, S] using
        (avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
          X x C D hD ω w q hq.le T hTpos δ hδpos hδanti hδlim))
  have hGB : ∀ m, (∫⁻ ω, G m ω ∂P) ≤ ENNReal.ofReal (w x) := by
    intro m
    have hδlt : δ m < T := div_lt_self hTpos (by
      have hn : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
    have hrpos : 0 < r m := by
      change 0 < Real.toNNReal (T - T / ((m : ℝ) + 2))
      rw [Real.toNNReal_pos]; exact sub_pos.mpr hδlt
    have hrlt : (r m : ℝ) < T := by
      have hpos : 0 < T - δ m := Real.toNNReal_pos.mp (hrpos)
      change (Real.toNNReal (T - δ m) : ℝ) < T
      rw [Real.coe_toNNReal _ (le_of_lt hpos)]
      exact sub_lt_self T (hδpos m)
    exact hPre (r m) hrpos hrlt
  change (∫ ω, Y ω ∂P) ≤ w x
  exact avram_ga_a565_two_stage_Fatou_expected_budget_bridge
    P (w x) hK Y F G hYm hYnn hFI hGm hFnear hGB hYnear

