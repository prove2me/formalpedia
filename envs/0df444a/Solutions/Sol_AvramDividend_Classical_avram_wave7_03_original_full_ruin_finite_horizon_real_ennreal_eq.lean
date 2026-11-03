-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:43:13.729201+00:00
-- url     : https://prove2.me/submissions/2d3dc4ad-ff51-48f0-aab2-160cad7c8d44

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original complete ruin-stopped signed Stieltjes integral and
    ENNReal cash agree at every finite horizon, with no extra mass premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have hSubset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) ⊆
        Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, ht.2⟩
  have hClosedLt :
      (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) < ⊤ := by
    rw [avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T]
    exact ENNReal.ofReal_lt_top
  have hMass :
      (dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hSubset) hClosedLt)
  exact avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq
    X x D hD ω (T : ℝ) (NNReal.coe_nonneg T) q hq hMass
