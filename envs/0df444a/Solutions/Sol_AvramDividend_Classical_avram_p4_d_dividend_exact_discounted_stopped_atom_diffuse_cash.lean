-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:12:11.54666+00:00
-- url     : https://prove2.me/submissions/0c68e805-c141-4ba5-90a4-59b1f3e5c7e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Exact discounted reward on the true paid set, including both measure parts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) := by
  classical
  obtain ⟨A, μatom, μdiffuse, hAc, hAm, hsplit, hatoms,
      hsupport, hdiffuse, hpaid⟩ :=
    avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse X x D hD ω T
  refine ⟨A, μatom, μdiffuse, hAc, hAm,
    hsplit, hatoms, hsupport, hdiffuse, ?_⟩
  let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)
  have hmeasure :
      (dividendMeasure D ω).restrict S =
        μatom.restrict S + μdiffuse.restrict S := hpaid
  change
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω).restrict S) =
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom.restrict S) +
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse.restrict S)
  rw [hmeasure]
  simp only [lintegral_add_measure]
