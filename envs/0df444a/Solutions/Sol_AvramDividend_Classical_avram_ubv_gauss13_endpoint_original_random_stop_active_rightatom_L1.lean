-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_random_stop_active_rightatom_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:14:54.49183+00:00
-- url     : https://prove2.me/submissions/4db6a04f-8222-4dd9-9897-58669e3d3863

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped right dividend atom is L1, including time zero and ruin exclusion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (σ ω : ℝ))) *
          (rightLimit D (σ ω) ω - D (σ ω) ω)
      else 0) P := by
  let Closed : Ω → ℝ := fun ω =>
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
  have hσmeas : Measurable (fun ω : Ω => (σ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable σ hσstop
  have hClosedI : Integrable Closed P :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q σ T hσmeas hσbound
  have hStrictI : Integrable Strict P :=
    avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
      X x C D hD q hq σ hσstop T hσbound
  have hAtomEq (ω : Ω) : Atom ω = Closed ω - Strict ω := by
    have hSplit :=
      avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
        X x C D hD ω q hq (σ ω)
    dsimp [Atom, Closed, Strict]
    linarith
  have hDiffI : Integrable (fun ω => Closed ω - Strict ω) P :=
    hClosedI.sub hStrictI
  exact hDiffI.congr (Filter.Eventually.of_forall fun ω => (hAtomEq ω).symm)
