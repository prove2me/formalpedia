-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_expected_horizon_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:25:01.647071+00:00
-- url     : https://prove2.me/submissions/79240436-b50c-43a0-b6c2-f3dcface8337

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_real_cash_split_ae
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_horizon_atom_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original discounted Stieltjes cash has an exact expectation
    partition into all payments before the horizon and its right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by
  let F : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let G : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let H : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hG : Integrable G P := by
    simpa only [G] using
      (avram_p3_bv_original_strict_cash_L1 X x C D hD q hq T hT)
  have hH : Integrable H P := by
    simpa only [H] using
      (avram_p3_bv_original_horizon_atom_L1 X x C D hD q hq T hT)
  have hSplit : F =ᵐ[P] (fun ω => G ω + H ω) := by
    change ∀ᵐ ω ∂P, F ω = G ω + H ω
    simpa only [F, G, H] using
      (avram_p3_bv_real_cash_split_ae X x C D hD q T hT)
  have hEq : (∫ ω, F ω ∂P) = (∫ ω, G ω ∂P) + (∫ ω, H ω ∂P) := by
    calc
      (∫ ω, F ω ∂P) = (∫ ω, G ω + H ω ∂P) := integral_congr_ae hSplit
      _ = (∫ ω, G ω ∂P) + (∫ ω, H ω ∂P) := integral_add hG hH
  simpa only [F, G, H] using hEq
