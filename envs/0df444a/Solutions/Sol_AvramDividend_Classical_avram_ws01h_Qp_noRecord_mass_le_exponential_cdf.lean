-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:40:53.029862+00:00
-- url     : https://prove2.me/submissions/54aa6ca8-d067-4e99-9984-c90ac3801f58

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
      (P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * q)))
    Qp {z : Ω × ℝ |
      (Real.toNNReal z.2 : ℝ≥0∞) < twoSidedExitUpTime X b z.1} ≤
      (ProbabilityTheory.expMeasure lam) (Iic b)) := by
  intro Qp
  have hM : Measurable (fun z : Ω × ℝ =>
      runningSup X z.2.toNNReal z.1) :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hLaw := esscher_positive_root_exp_clock_supremum_full_law_ws01d
    X φ q hφ hq hroot p hp lam hlam hshift
  have hCDF : Qp {z : Ω × ℝ |
      ¬ b < runningSup X z.2.toNNReal z.1} =
      (ProbabilityTheory.expMeasure lam) (Iic b) := by
    have h := congrArg (fun μ : Measure ℝ => μ (Iic b)) hLaw
    rw [Measure.map_apply hM measurableSet_Iic] at h
    simpa only [Set.preimage, Set.mem_Iic, not_lt, Set.mem_setOf_eq] using h
  calc
    Qp {z : Ω × ℝ |
        (Real.toNNReal z.2 : ℝ≥0∞) < twoSidedExitUpTime X b z.1} ≤
      Qp {z : Ω × ℝ |
        ¬ b < runningSup X z.2.toNNReal z.1} := by
        apply measure_mono
        intro z hz
        change ¬ b < runningSup X (Real.toNNReal z.2) z.1
        intro hsup
        have hhit :=
          (avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
            X b hb z.1 (Real.toNNReal z.2)).mp hsup
        have ht : twoSidedExitUpTime X b z.1 <
            (Real.toNNReal z.2 : ℝ≥0∞) := by
          simpa only [twoSidedExitUpTime] using hhit
        exact (lt_asymm hz) ht
    _ = _ := hCDF
