-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_cash_full_real_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:25:28.733148+00:00
-- url     : https://prove2.me/submissions/48d01461-ed88-46c8-bf1a-1044a83e5587

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original ruin-stopped Cash is a summable real right-atom series plus diffuse Cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict
        (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      Summable (fun a : A =>
        ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
          μatom {a.1}).toReal) ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂
          (dividendMeasure D ω)).toReal =
        (∑' a : A,
          ((if a.1 ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * a.1))) else 0) *
            μatom {a.1}).toReal) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * s))) else 0)
            ∂μdiffuse).toReal := by
  rcases avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
      X x D hD q hq ω T with
    ⟨A, μatom, μdiffuse, hA, hAmeas, hsplit, hdiff,
      hAtomSupport, hDiffuseSupport, htotal, hRight, hCashEq⟩
  obtain ⟨hsum, hconvert⟩ :=
    avram_p4_f_assembly_original_cash_real_atomic_series
      X x D ω T A hA μatom μdiffuse hsplit htotal q hq
  refine ⟨A, μatom, μdiffuse, hA, hAmeas, hsplit, hdiff,
    hAtomSupport, hDiffuseSupport, hsum, ?_⟩
  rw [hconvert] at hCashEq
  exact hCashEq
