-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:47:44.972008+00:00
-- url     : https://prove2.me/submissions/5d00e865-dc27-4f8e-b99b-4cc30c90b7de

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Unconditional exact complete original stopped real/ENNReal cash
    expectation bridge at bounded measurable random clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hMass : ∀ᵐ ω ∂P,
      (dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ)) ≠ ⊤ := by
    apply Filter.Eventually.of_forall
    intro ω
    have hSubset :
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) ⊆
          Icc (0 : ℝ) (τ ω : ℝ) := by
      intro t ht
      exact ⟨ht.1.1, ht.2⟩
    have hClosedLt :
        (dividendMeasure D ω) (Icc (0 : ℝ) (τ ω : ℝ)) < ⊤ := by
      rw [avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hDiv ω (τ ω)]
      exact ENNReal.ofReal_lt_top
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hSubset) hClosedLt)
  exact avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
    X x C D hD q hq T τ hτBound hτMeas hMass
