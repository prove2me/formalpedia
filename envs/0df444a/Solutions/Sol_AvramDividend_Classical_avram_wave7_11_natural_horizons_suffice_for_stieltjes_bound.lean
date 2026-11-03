-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_natural_horizons_suffice_for_stieltjes_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:04:35.507724+00:00
-- url     : https://prove2.me/submissions/d337ffaf-f8fa-4ed5-8850-73dab82ad458

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A uniform bound at integer horizons also bounds every real horizon,
    preserving all original-source discounted Stieltjes dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞) (q : ℝ) (B : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B)
    (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B := by
  obtain ⟨n, hn⟩ := exists_nat_gt T
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
      apply MeasureTheory.lintegral_mono
      intro ω
      apply MeasureTheory.lintegral_mono_set
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hn.le⟩
    _ ≤ B := hBound n
