-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a568_BV_true_strict_terminal_reward_measurable_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:57:08.460411+00:00
-- url     : https://prove2.me/submissions/62d17902-4bb4-4542-8cbc-ff85fad842a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
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
    (hactivity : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let Y : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    (∀ᵐ ω ∂P, 0 ≤ Y ω) ∧ AEStronglyMeasurable Y P := by
  classical
  intro δ S F Y
  obtain ⟨hδpos, _, hδanti, hδlim⟩ :=
    avram_a19_uniform_delta_profile T hTpos
  have hFI : ∀ n, Integrable (F n) P :=
    avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hTpos
  constructor
  · filter_upwards [] with ω
    dsimp [Y]
    have hCash : 0 ≤
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal :=
      ENNReal.toReal_nonneg
    split_ifs with hs
    · have hwT : 0 ≤ w (riskProcess X x D S ω) :=
        hw_nonneg ω S hTpos hs
      have he : 0 ≤ Real.exp (-(q * T)) := (Real.exp_pos _).le
      nlinarith
    · simpa using hCash
  · apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hFI n).aestronglyMeasurable)
    filter_upwards [] with ω
    have hc :=
      avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
        X x C D hD ω q hq.le T hTpos δ hδpos hδanti hδlim
    simpa only [Y, F, δ, S] using
      hc.add (tendsto_const_nhds (x :=
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0))
