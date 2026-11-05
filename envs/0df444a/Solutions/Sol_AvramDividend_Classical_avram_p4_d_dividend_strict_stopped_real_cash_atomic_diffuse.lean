-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_strict_stopped_real_cash_atomic_diffuse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:23:51.027598+00:00
-- url     : https://prove2.me/submissions/3410bc47-1aee-4a7b-8412-4e25bb284a51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact real-valued original stopped cash split, with both atom and diffuse terms finite at a strict surviving horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) < ⊤ ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) < ⊤ ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse).toReal := by
  obtain ⟨A, μatom, μdiffuse, hcount, hmeas, hmeasure,
      hatom, hzero, hdiffuse, hsplit⟩ :=
    avram_p4_d_dividend_exact_discounted_stopped_atom_diffuse_cash
      X x D hD ω T q
  have hbound :=
    avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
      X x D hD q hq ω T hstrict
  have htotal :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) < ⊤ :=
    lt_of_le_of_lt hbound (by simp)
  have hboth :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) < ⊤ ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) < ⊤ := by
    apply ENNReal.add_lt_top.mp
    rw [← hsplit]
    exact htotal
  refine ⟨A, μatom, μdiffuse, hcount, hmeas, hmeasure, hatom, hzero,
    hdiffuse, hboth.1, hboth.2, ?_⟩
  rw [hsplit]
  exact ENNReal.toReal_add (ne_of_lt hboth.1) (ne_of_lt hboth.2)