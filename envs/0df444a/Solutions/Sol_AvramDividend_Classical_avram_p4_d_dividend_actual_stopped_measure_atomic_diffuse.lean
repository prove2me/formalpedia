-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:00:55.736499+00:00
-- url     : https://prove2.me/submissions/a72b3736-24ce-481d-bd9b-33464c9215dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Restrict the genuine finite-window control measure to the source's true paid set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) =
        μatom.restrict (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) +
        μdiffuse.restrict (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) := by
  classical
  let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)
  have hSmeas : MeasurableSet S := by
    dsimp [S, paymentTimes]
    measurability
  have hSsub : S ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro t ht
    rcases ht with ⟨htpay, htT⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at htpay
    exact ⟨htpay.1, htT⟩
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas, hsplit,
      hatoms, hsupport, hdiffuse, _, _⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse D hD ω T
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hsplit, hatoms, hsupport, hdiffuse, ?_⟩
  have hrestrict :
      ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict S =
        (dividendMeasure D ω).restrict S := by
    rw [Measure.restrict_restrict hSmeas]
    rw [Set.inter_eq_left.mpr hSsub]
  change (dividendMeasure D ω).restrict S =
    μatom.restrict S + μdiffuse.restrict S
  calc
    (dividendMeasure D ω).restrict S =
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))).restrict S :=
      hrestrict.symm
    _ = (μatom + μdiffuse).restrict S := by rw [hsplit]
    _ = μatom.restrict S + μdiffuse.restrict S := by rw [Measure.restrict_add]
