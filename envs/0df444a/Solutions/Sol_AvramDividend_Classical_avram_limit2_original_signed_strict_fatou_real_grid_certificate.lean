-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_strict_fatou_real_grid_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:16:26.979349+00:00
-- url     : https://prove2.me/submissions/2349b4f2-69d7-4d44-872d-4d34756c6651

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Exact original signed strict stopped Stieltjes cash and pre-rightpayment
    terminal Fatou grid passage, without asserting cash is finite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Term : Ω → ℝ)
    (F : ℕ → Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hFmeas : ∀ n, Measurable (F n))
    (hMean : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ B)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ≤
        liminf (fun n : ℕ => F n ω) atTop) :
    (∫⁻ ω, ENNReal.ofReal
      (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B := by
  calc
    _ ≤ (∫⁻ ω, liminf (fun n : ℕ => F n ω) atTop ∂P) := by
      exact lintegral_mono_ae hFatou
    _ ≤ liminf (fun n : ℕ => ∫⁻ ω, F n ω ∂P) atTop := by
      exact lintegral_liminf_le hFmeas
    _ ≤ B := by
      apply Filter.liminf_le_of_le
      · exact ⟨0, Filter.Eventually.of_forall
          (fun y : ℝ≥0∞ => bot_le)⟩
      · intro b hb
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hMean n)
