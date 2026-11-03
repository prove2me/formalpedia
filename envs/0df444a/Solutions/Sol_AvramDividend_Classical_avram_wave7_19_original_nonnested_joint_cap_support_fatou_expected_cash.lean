-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:47:25.435809+00:00
-- url     : https://prove2.me/submissions/4771f5e8-ec83-4f7b-82af-df3c7ef62ff4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact expected source ruin cash under arbitrary eventual nonnested cap-plus-interior supports. -/
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
    (hEventual : ∀ᵐ ω ∂P,
      ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ∀ᶠ n : ℕ in Filter.atTop, t ∈ boundary ω ∪ interior n ω)
    (budget : ℝ≥0∞)
    (hBudgetLiminf : Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)
      Filter.atTop ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  let L (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in boundary ω ∪ interior n ω,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let B (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hLMeas : ∀ n, Measurable (L n) := by
    intro n
    exact avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
      D hD {p : ℝ × Ω | p.1 ∈ boundary p.2 ∪ interior n p.2} (hJoint n) q
  have hPath : ∀ᵐ ω ∂P, B ω ≤
      Filter.liminf (fun n : ℕ => L n ω) Filter.atTop := by
    filter_upwards [hEventual] with ω hω
    exact avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
      X q x T D ω (boundary ω) (fun n => interior n ω)
      (hBoundaryMeas ω) (fun n => hInteriorMeas n ω) hω
  change (∫⁻ ω, B ω ∂P) ≤ budget
  calc
    (∫⁻ ω, B ω ∂P) ≤
        ∫⁻ ω, Filter.liminf (fun n : ℕ => L n ω) Filter.atTop ∂P :=
      lintegral_mono_ae hPath
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ ω, L n ω ∂P) Filter.atTop :=
      lintegral_liminf_le hLMeas
    _ ≤ budget := hBudgetLiminf
