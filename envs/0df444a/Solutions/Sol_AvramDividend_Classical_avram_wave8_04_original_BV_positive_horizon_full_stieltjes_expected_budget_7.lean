-- Prove2me | solution 7 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_full_stieltjes_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:29:51.596716+00:00
-- url     : https://prove2.me/submissions/d5fe918d-771b-4049-a621-7474705ef274
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_topcap_original_full_T_strict_cash_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
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
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  classical
  intro S Term
  have hSpos : 0 < S := by exact_mod_cast hTpos
  let CashClosed : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
       Real.exp (-(q * T)) * w (riskProcess X x D S ω)
     else 0)
  have hCashTerm :=
    avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
      X hBV q w hw_cont hw_neg x C D hD T hT
  have hClosed : Integrable CashClosed P := by
    simpa only [CashClosed] using hCashTerm.1
  have hTerm : Integrable Term P := by
    simpa only [Term, S] using hCashTerm.2
  have hY : Integrable Y P := by
    simpa only [Y, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q hq.le T hT)
  have hTermEq (ω : Ω) : Term ω =
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) else 0) := by
    have hPost :=
      (avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
        X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD q hjump ω S).1
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · have hp : 0 ≤ Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) := by
        simpa only [hs, if_pos, show (S : ℝ) = T from rfl] using hPost
      simp [Term, hs, hp]
    · simp [Term, hs]
  have hPoint (ω : Ω) : CashClosed ω + Term ω ≤ Y ω := by
    rw [hTermEq]
    simpa only [CashClosed, Y, show (S : ℝ) = T from rfl] using
      (avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
        X x C D hD w q hq.le S hSpos hjump ω)
  have hStrict : (∫ ω, Y ω ∂P) ≤ w x := by
    by_cases htop : C = ⊤
    · simpa only [Y, S] using
        (avram_bv_topcap_original_full_T_strict_cash_expected_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos htop)
    · simpa only [Y, S] using
        (avram_a19_finite_cap_original_full_T_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos htop)
  calc
    (∫ ω, CashClosed ω ∂P) + (∫ ω, Term ω ∂P) =
        (∫ ω, CashClosed ω + Term ω ∂P) :=
      (integral_add hClosed hTerm).symm
    _ ≤ (∫ ω, Y ω ∂P) :=
      integral_mono (hClosed.add hTerm) hY hPoint
    _ ≤ w x := hStrict
