-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_Qp_closed_survival_small_rate_CDF_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:38:22.69033+00:00
-- url     : https://prove2.me/submissions/5ad3849a-0667-4ea0-a8fa-aaf22a34d181

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Exact original continuous-source Lévy nonruin event under genuine
finite terminal Qp tends to the perpetual Esscher survival law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (ν : Measure ℝ)
    (hν : ν (Iic x) =
       (⨅ t : ℝ≥0, ENNReal.ofReal
         (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t →
           0 ≤ x + X.X s ω}).indicator
           (fun ω => Real.exp (θ * X.X t ω -
             (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n : ℕ =>
      ((P.prod (expMeasure (p n))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
        {z : Ω × ℝ | ∀ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1})
      atTop (𝓝 (ν (Iic x))) := by
  have hEvent :=
    avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival X x
  have hLim := esscher_true_joint_clock_cdf_tendsto_perpetual
    X θ hθ x ν hν p hp hpos
  simpa only [hEvent] using hLim
