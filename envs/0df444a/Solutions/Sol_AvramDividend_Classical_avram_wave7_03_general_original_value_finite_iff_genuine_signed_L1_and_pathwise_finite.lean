-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:45:19.391263+00:00
-- url     : https://prove2.me/submissions/a5e950cc-1793-42ed-b79a-a7e086ff74e2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At any real discount, the canonical expected original ENNReal cash is
    finite precisely when the actual unrestricted signed real Stieltjes
    payout is L1(P) and the source fibre cash is finite P-almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (dividendValue X q x D < ⊤) ↔
      Integrable (fun ω : Ω =>
        ∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
      (∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) < ⊤) := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hEq (hFin : ∀ᵐ ω ∂P, F ω < ⊤) :
      (fun ω => (F ω).toReal) =ᵐ[P] g := by
    filter_upwards [hFin] with ω hω
    have hPath :=
      avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
        X x D hD ω q hω
    have hgNN : 0 ≤ g ω := by
      apply integral_nonneg
      intro t
      exact (Real.exp_pos (-(q * t))).le
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal hPath.2.symm
      _ = g ω := ENNReal.toReal_ofReal hgNN
  constructor
  · intro hValue
    have hBase :=
      (avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
        X x D hD q).1 hValue
    exact ⟨hBase.1.congr (hEq hBase.2), hBase.2⟩
  · rintro ⟨hGInt, hFin⟩
    have hFInt : Integrable (fun ω => (F ω).toReal) P :=
      hGInt.congr (hEq hFin).symm
    exact (avram_wave7_03_original_perpetual_cash_finite_iff_toReal_L1_and_ae_finite
      X x D hD q).2 ⟨hFInt, hFin⟩
