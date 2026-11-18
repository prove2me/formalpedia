-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:35:44.246175+00:00
-- url     : https://prove2.me/submissions/8e442937-63e5-45ad-b40e-4aa29575e77c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
import Theorems.Thm_AvramDividend_Classical_avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Real original stopped strict cash is at least endpoint-discounted barrier dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) (hq : 0 ≤ q)
    (hFin : (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤) :
    Real.exp (-(q * (S : ℝ))) *
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal := by
  have hDzero :
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) 0 ω = 0 := by
    simp [barrierStrategy]
  have hDnonneg :
      0 ≤ barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω := by
    unfold barrierStrategy
    split_ifs <;> positivity
  have hCell :=
    avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
      X (1 / 8 : ℝ) ω q hq (0 : ℝ) (S : ℝ)
  have hSub :=
    avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
      X ω S T hST hTube q
  have hBound :
      ENNReal.ofReal (Real.exp (-(q * (S : ℝ)))) *
        ENNReal.ofReal
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω) ≤
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) := by
    have hCell' := hCell
    simp only [Real.toNNReal_coe, Real.toNNReal_zero, hDzero, sub_zero] at hCell'
    exact hCell'.trans hSub
  have hMul :
      ENNReal.ofReal
        (Real.exp (-(q * (S : ℝ))) *
          barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω) ≤
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) := by
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    exact hBound
  have hRes := ENNReal.toReal_mono hFin hMul
  have hNonneg : 0 ≤ Real.exp (-(q * (S : ℝ))) *
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hDnonneg
  rw [ENNReal.toReal_ofReal hNonneg] at hRes
  exact hRes
