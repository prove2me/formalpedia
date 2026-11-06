-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_vanishing_error_grid_to_actual_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:36:54.42186+00:00
-- url     : https://prove2.me/submissions/f6eba9b6-0bd8-400e-aa59-edacf9b04cfb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_vanishing_error_signed_fatou_original_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Signed physical finite-grid cash and terminal budgets with vanishing
discretisation error imply the exact original strict-horizon budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (hTpos : 0 < T)
    (F R : ℕ → Ω → ℝ) (ε : ℕ → ℝ)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hErr : Tendsto ε atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + R n ω + ε n)
    (hFatou : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      ENNReal.ofReal (
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hYInt : Integrable Y P :=
    avram_p3_bv_original_prebudget_L1 X hBV
      x C D hD w hw_cont hw_neg q hq T hT
  have hSpos : 0 < S := by
    exact_mod_cast hTpos
  have hYNonneg : 0 ≤ᵐ[P] Y := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [Y]
    apply add_nonneg
    · exact ENNReal.toReal_nonneg
    · split_ifs with hsurv
      · exact mul_nonneg (le_of_lt (Real.exp_pos _))
          (hw_nonneg ω S hSpos hsurv)
      · exact le_refl 0
  have hFatou' : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop := by
    simpa only [Y, S] using hFatou
  letI : IsProbabilityMeasure P := X.isProbability
  have hExpected := avram_p3_2_vanishing_error_signed_fatou_original_grid
    P (w x) Y F R ε hYInt hYNonneg hFMeas hFInt hFNonneg
    hR hErr hBound hFatou'
  change (∫ ω, Y ω ∂P) ≤ w x
  exact hExpected
