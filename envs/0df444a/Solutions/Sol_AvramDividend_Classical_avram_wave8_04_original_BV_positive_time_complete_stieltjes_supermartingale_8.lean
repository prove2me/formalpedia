-- Prove2me | solution 8 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_time_complete_stieltjes_supermartingale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:32:27.115653+00:00
-- url     : https://prove2.me/submissions/f4870fd4-422a-4812-87f4-619481c08529
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0
    Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x := by
  classical
  intro S Term
  let Raw : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω) else 0
  have hRawNonneg : ∀ ω, 0 ≤ Raw ω := by
    intro ω
    have hST : (S : ℝ) = T := rfl
    simpa [Raw, hST] using
      (avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
        X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD q hjump ω S).1
  have hTermEq : Term = Raw := by
    funext ω
    dsimp [Term, Raw]
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · simp only [if_pos hs]
      have hR : 0 ≤ Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) := by
        simpa only [Raw, if_pos hs] using hRawNonneg ω
      exact max_eq_right hR
    · simp [hs]
  have hRawI : Integrable Raw P := by
    have hST : (S : ℝ) = T := rfl
    simpa [Raw, hST] using
      (avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
        X hX hBV q hq w hw_cont hw0 hw_neg C hC
        hw_smooth hw_grad x hxc D hD S (fun _ : Ω => S)
        measurable_const (by intro ω; exact le_rfl))
  have hTermI : Integrable Term P := by
    rw [hTermEq]
    exact hRawI
  have hSigned :=
    avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump T hT hTpos
  refine ⟨hTermI, ?_⟩
  rw [hTermEq]
  simpa only [Raw, S] using hSigned
