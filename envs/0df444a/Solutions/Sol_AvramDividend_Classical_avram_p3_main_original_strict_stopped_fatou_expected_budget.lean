-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_strict_stopped_fatou_expected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:02:07.209+00:00
-- url     : https://prove2.me/submissions/9580ed60-6eeb-46fc-810c-7e5812b5cd0b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Fatou transfers bounded original localised nonnegative payoffs to the
exact strict-horizon cash and killed pre-rightpayment terminal in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hwx : 0 ≤ w x)
    (F : ℕ → Ω → ℝ≥0∞) (hFmeas : ∀ n, Measurable (F n))
    (hLiminf : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (riskProcess X x D S ω)
        else 0)) ≤ liminf (fun n => F n ω) atTop)
    (hBudget : ∀ n,
      (∫⁻ ω, F n ω ∂P) ≤ ENNReal.ofReal (w x)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let G : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hGI : Integrable G P := by
    simpa only [G, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q hq T hT)
  have hSpos : (0 : ℝ≥0) < S := by exact_mod_cast hTpos
  have hGpos : 0 ≤ᵐ[P] G := by
    apply Filter.Eventually.of_forall
    intro ω
    have hTerm : 0 ≤ (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) := by
      split_ifs with hs
      · exact mul_nonneg (le_of_lt (Real.exp_pos _))
          (hw_nonneg ω S hSpos hs)
      · exact le_refl _
    exact add_nonneg ENNReal.toReal_nonneg hTerm
  have hFatou :
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) ≤
      liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := by
    calc
      _ ≤ (∫⁻ ω, liminf (fun n => F n ω) atTop ∂P) := by
        apply lintegral_mono_ae
        filter_upwards [hLiminf] with ω hω
        exact hω
      _ ≤ _ := lintegral_liminf_le hFmeas
  have hLiminfBudget :
      liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop ≤
        ENNReal.ofReal (w x) := by
    refine Filter.liminf_le_of_le (hf := by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ :=
      (hb.and (Filter.Eventually.of_forall hBudget)).exists
    exact le_trans hn.1 hn.2
  have hExpected :
      ENNReal.ofReal (∫ ω, G ω ∂P) ≤ ENNReal.ofReal (w x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hGI hGpos]
    exact le_trans hFatou hLiminfBudget
  exact (ENNReal.ofReal_le_ofReal_iff hwx).mp hExpected
