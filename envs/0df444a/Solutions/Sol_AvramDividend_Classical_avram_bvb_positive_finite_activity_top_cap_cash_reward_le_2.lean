-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_positive_finite_activity_top_cap_cash_reward_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:01:10.024972+00:00
-- url     : https://prove2.me/submissions/36029c53-5d56-494f-a087-5dc62ee154ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_top_cap_expected_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Direct source-faithful result from the Proved BV single-clock budget.
   Keeps the original physical strict prefix T-T/(n+2), terminal at T,
   prepayment reserve and ruin clock. No residual-L1 assumption is needed. -/

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
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapTop : C = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  classical
  intro δ S F n
  have hδpos : 0 < δ n := by
    change 0 < T / ((n : ℝ) + 2)
    positivity
  have hδle : δ n ≤ T := by
    change T / ((n : ℝ) + 2) ≤ T
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc
      T / ((n : ℝ) + 2) ≤ T / 1 :=
        div_le_div_of_nonneg_left hT.le (by norm_num) hden
      _ = T := by ring
  have hs0 : 0 ≤ T - δ n := sub_nonneg.mpr hδle
  have hsT : T - δ n < T := sub_lt_self T hδpos
  have hSource :=
    avram_redux6_bv_single_clock_top_cap_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT.le hT hCapTop (T - δ n) hs0 hsT
  simpa only [F, δ, S] using hSource
