-- Prove2me | solution 1 for AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_tail_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:39:50.704469+00:00
-- url     : https://prove2.me/submissions/4d456b34-2afd-46ac-8b83-7cb46ca46f57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Strict exponential-observation-time supremum tail under the genuine product law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (b : ℝ) (hb : 0 < b) :
    (P.prod (ProbabilityTheory.expMeasure p))
      {z : Ω × ℝ | b < runningSup X z.2.toNNReal z.1} =
    ENNReal.ofReal (Real.exp (-(lam * b))) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let τ : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTimeCorrected X b ω
  have hb0 : 0 ≤ b := le_of_lt hb
  have hm : Measurable (fun z : Ω × ℝ =>
      runningSup X z.2.toNNReal z.1) :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hs : MeasurableSet {z : Ω × ℝ |
      b < runningSup X z.2.toNNReal z.1} :=
    measurableSet_lt measurable_const hm
  have hsection (ω : Ω) :
      (ProbabilityTheory.expMeasure p)
        (Prod.mk ω ⁻¹' {z : Ω × ℝ |
          b < runningSup X z.2.toNNReal z.1}) =
      if τ ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (-(p * (τ ω).toReal))) else 0 := by
    have hpass (t : ℝ) :
        b < runningSup X t.toNNReal ω ↔
          τ ω < (t.toNNReal : ℝ≥0∞) := by
      have hh :=
        avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
          X b hb0 ω t.toNNReal
      change b < runningSup X t.toNNReal ω ↔
        τ ω < (t.toNNReal : ℝ≥0∞) at hh
      exact hh
    by_cases hfin : τ ω < (⊤ : ℝ≥0∞)
    · have hne : τ ω ≠ ⊤ := ne_top_of_lt hfin
      have hset :
          (Prod.mk ω ⁻¹' {z : Ω × ℝ |
            b < runningSup X z.2.toNNReal z.1}) =
          {t : ℝ | (τ ω).toNNReal < t.toNNReal} := by
        ext t
        change (b < runningSup X t.toNNReal ω) ↔
          (τ ω).toNNReal < t.toNNReal
        rw [hpass t, ← ENNReal.coe_toNNReal hne]
        simp
      rw [hset, avram_ws01e_b_exp_clock_toNNReal_strict_tail
        p hp (τ ω).toNNReal]
      simp only [if_pos hfin, ENNReal.toReal]
    · have htop : τ ω = ⊤ := top_unique (not_lt.mp hfin)
      have hset :
          (Prod.mk ω ⁻¹' {z : Ω × ℝ |
            b < runningSup X z.2.toNNReal z.1}) =
          (∅ : Set ℝ) := by
        ext t
        change (b < runningSup X t.toNNReal ω) ↔ False
        rw [hpass t, htop]
        simp
      rw [hset]
      simp [hfin]
  calc
    (P.prod (ProbabilityTheory.expMeasure p))
        {z : Ω × ℝ | b < runningSup X z.2.toNNReal z.1} =
      ∫⁻ ω, (ProbabilityTheory.expMeasure p)
        (Prod.mk ω ⁻¹' {z : Ω × ℝ |
          b < runningSup X z.2.toNNReal z.1}) ∂P :=
      Measure.prod_apply hs
    _ = ∫⁻ ω, if τ ω < (⊤ : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp (-(p * (τ ω).toReal))) else 0 ∂P := by
      congr 1
      funext ω
      exact hsection ω
    _ = ENNReal.ofReal (Real.exp (-(lam * b))) := by
      simpa only [τ] using
        levy_positive_root_exact_strict_upcrossing_discount
          X p hp lam hlam hroot b hb
