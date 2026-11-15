-- Prove2me | solution 3 for AvramDividend.Classical.avram_bvb_original_BV_every_inner_horizon_expected_cash_terminal_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:49:01.675978+00:00
-- url     : https://prove2.me/submissions/8fc59e20-d6af-4bf4-8399-1645c2ddde69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux6_bv_single_clock_top_cap_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_finitecap_original_strict_physical_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Original finite-activity BV expected cash bound by cap case split.
   The finite-cap core is independent original strict HJB source b19562c5. -/

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
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
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
  by_cases hTop : C = ⊤
  · have hSource :=
      avram_redux6_bv_single_clock_top_cap_expected_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        T hT.le hT hTop (T - δ n) hs0 hsT
    simpa only [F, δ, S] using hSource
  · have hSource :=
      avram_bv_finitecap_original_strict_physical_expected_cash_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTop
    simpa only [F, δ, S] using hSource n
