-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_joint_support_cap_retaining_full_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:30:30.964129+00:00
-- url     : https://prove2.me/submissions/8697298e-cfe2-4a3b-824d-0c73aecefc45

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Complete source ruin cash from jointly measurable cap-plus-interior stopped Ito supports. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (boundary : Ω → Set ℝ) (interior : ℕ → Ω → Set ℝ)
    (hBoundaryMeas : ∀ ω, MeasurableSet (boundary ω))
    (hInteriorMeas : ∀ n ω, MeasurableSet (interior n ω))
    (hJoint : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ boundary p.2 ∪ interior n p.2})
    (hInteriorMon : ∀ ω, Monotone (fun n => interior n ω))
    (hCover : ∀ᵐ ω ∂P,
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        ⋃ n : ℕ, boundary ω ∪ interior n ω)
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  have hCashMeas (n : ℕ) :
      Measurable (fun ω : Ω =>
        ∫⁻ t in boundary ω ∪ interior n ω,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    exact avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
      D hD {p : ℝ × Ω | p.1 ∈ boundary p.2 ∪ interior n p.2} (hJoint n) q
  exact avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
    X q x T D hD boundary interior hBoundaryMeas hInteriorMeas
    hInteriorMon hCover hCashMeas budget hBudget
