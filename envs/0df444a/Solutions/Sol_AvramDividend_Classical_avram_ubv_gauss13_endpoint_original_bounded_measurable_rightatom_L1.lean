-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_bounded_measurable_rightatom_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:58:25.542511+00:00
-- url     : https://prove2.me/submissions/1990d9aa-b558-4975-96ce-5a7eda694412

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-exact measurable right dividend atom, dominated by full stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable (fun ω : Ω => (σ ω : ℝ)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (σ ω : ℝ))) *
          (rightLimit D (σ ω) ω - D (σ ω) ω)
      else 0) P := by
  let Full : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal
  let Atom : Ω → ℝ := fun ω =>
    if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (σ ω : ℝ))) *
        (rightLimit D (σ ω) ω - D (σ ω) ω)
    else 0
  have hFullI : Integrable Full P :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q σ T hσmeas hσbound
  have hStrictI : Integrable Strict P :=
    avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
      X x C D hD q hq σ hσmeas T hσbound
  have hSplit (ω : Ω) : Full ω = Strict ω + Atom ω := by
    simpa only [Full, Strict, Atom] using
      (avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
        X x C D hD ω q hq (σ ω))
  have hAtomDiff (ω : Ω) : Full ω - Strict ω = Atom ω := by
    linarith [hSplit ω]
  have hAtomMeas : AEStronglyMeasurable Atom P :=
    (hFullI.aestronglyMeasurable.sub hStrictI.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall hAtomDiff)
  have hAtomNN : ∀ᵐ ω ∂P, 0 ≤ Atom ω := by
    filter_upwards [] with ω
    by_cases ha : σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω
    · simpa only [Atom, if_pos ha] using
        (mul_nonneg (le_of_lt (Real.exp_pos (-(q * (σ ω : ℝ)))))
          (sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1.1 ω (σ ω))))
    · simp [Atom, ha]
  have hAtomLe : ∀ᵐ ω ∂P, Atom ω ≤ Full ω := by
    filter_upwards [] with ω
    have hStrictNN : 0 ≤ Strict ω := ENNReal.toReal_nonneg
    linarith [hSplit ω]
  exact hFullI.mono_nonneg hAtomMeas hAtomNN hAtomLe
