-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_payment_supported_cash_atoms_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:24:34.105862+00:00
-- url     : https://prove2.me/submissions/e4808240-82bc-4654-9fd5-0d084cc5c8da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_atomic_series
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True source payment-time support removes the Cash indicator from summability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (hA : A.Countable)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (htotal : ((dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ))) Set.univ =
        ENNReal.ofReal (rightLimit D T ω))
    (q : ℝ) (hq : 0 ≤ q)
    (hPay : ∀ a : A, a.1 ∈ paymentTimes (ruinTime X x D ω)) :
    Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal) := by
  have h := (avram_p4_f_assembly_original_cash_real_atomic_series
    X x D ω T A hA μatom μdiffuse hsplit htotal q hq).1
  simpa [hPay] using h
