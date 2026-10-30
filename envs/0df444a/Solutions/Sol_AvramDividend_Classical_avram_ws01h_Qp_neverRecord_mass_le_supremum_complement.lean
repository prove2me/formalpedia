-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_Qp_neverRecord_mass_le_supremum_complement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:45:20.124097+00:00
-- url     : https://prove2.me/submissions/2337f45d-fd58-48b5-a19d-d3c97e20ecd3

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
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
    (b : ℝ) (hb : 0 ≤ b) (φ p : ℝ) (hp : 0 < p) :
    (let Qp : Measure (Ω × ℝ) :=
      (P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
    Qp {z : Ω × ℝ |
      (Real.toNNReal z.2 : ℝ≥0∞) < twoSidedExitUpTime X b z.1} ≤
    Qp {z : Ω × ℝ |
      ¬ b < runningSup X (Real.toNNReal z.2) z.1}) := by
  intro Qp
  apply measure_mono
  intro z hz
  change ¬ b < runningSup X (Real.toNNReal z.2) z.1
  intro hsup
  have hhit :=
    (avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
      X b hb z.1 (Real.toNNReal z.2)).mp hsup
  have htime : twoSidedExitUpTime X b z.1 <
      (Real.toNNReal z.2 : ℝ≥0∞) := by
    simpa only [twoSidedExitUpTime] using hhit
  exact (lt_asymm hz) htime
