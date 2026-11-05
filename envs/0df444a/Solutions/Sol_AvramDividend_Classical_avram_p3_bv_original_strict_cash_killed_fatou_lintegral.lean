-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_killed_fatou_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:42:16.573197+00:00
-- url     : https://prove2.me/submissions/5ac4fe13-f562-453f-9608-934038203bd1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Fatou's lemma on the actual original strict Stieltjes cash plus killed
terminal process. All pathwise and measurability premises remain explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (S : ℝ≥0) (u : ℕ → ℝ≥0) :
    let F : ℝ≥0 → Ω → ℝ≥0∞ := fun s ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (s : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ENNReal.ofReal
        (if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω)
        else 0);
    (∀ n, Measurable (F (u n))) →
    (∀ᵐ ω ∂P, F S ω ≤ Filter.liminf (fun n => F (u n) ω) atTop) →
    (∫⁻ ω, F S ω ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, F (u n) ω ∂P) atTop := by
  dsimp only
  intro hmeas hpath
  exact (lintegral_mono_ae hpath).trans (lintegral_liminf_le hmeas)
