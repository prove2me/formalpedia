-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_real_exp_clock_lower_age_tie_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:59:11.93864+00:00
-- url     : https://prove2.me/submissions/0fe82fd2-06fe-464f-b497-825ca074ab45

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The real Exp(p) terminal observation never equals the actual lower strict
first-passage age under the true terminally tilted joint Lévy law Qp. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitDownTime X lower ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = 0) := by
  intro age Qp
  have hLower : Measurable (twoSidedExitDownTime X lower) := by
    have hs :=
      (avram_ws01h_lowerPassage_stopping_rightCont_filtration
        X lower).measurable_iSup
    exact hs.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
  have hage : Measurable (fun ω => ((age ω : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp
      (ENNReal.measurable_toNNReal.comp hLower)
  have hS : MeasurableSet
      {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} :=
    measurableSet_eq_fun measurable_snd (hage.comp measurable_fst)
  have := isProbabilityMeasure_expMeasure hp
  apply withDensity_absolutelyContinuous
  rw [Measure.prod_apply hS]
  have h0 : ∀ ω, expMeasure p
      (Prod.mk ω ⁻¹' {z : Ω × ℝ |
        z.2 = (age z.1 : ℝ)}) = 0 := by
    intro ω
    have hFibre :
        Prod.mk ω ⁻¹' {z : Ω × ℝ |
          z.2 = (age z.1 : ℝ)} =
          {((age ω : ℝ≥0) : ℝ)} := by
      ext r
      simp
    rw [hFibre]
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  exact (lintegral_congr fun ω => h0 ω).trans lintegral_zero
