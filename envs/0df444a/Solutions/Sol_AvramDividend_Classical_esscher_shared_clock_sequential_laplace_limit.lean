-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shared_clock_sequential_laplace_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:24:07.522183+00:00
-- url     : https://prove2.me/submissions/ea6d7527-a99e-427e-bc0e-7ad80b91f78f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_esscher_shared_clock_pathwise_limit
import Theorems.Thm_AvramDividend_Classical_esscher_infimum_bounded_laplace_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set

/-- Bounded exponential transforms converge under a shared horizon coupling. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q]
    (E : Ω → ℝ) (Y : ℝ → Ω → ℝ) (Yinf : Ω → ℝ)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hE : ∀ᵐ ω ∂Q, 0 < E ω)
    (hY : ∀ᵐ ω ∂Q,
      Tendsto (fun t : ℝ => Y t ω) atTop (nhds (Yinf ω)))
    (β : ℝ) (hβ : 0 < β)
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω => Real.exp (-β * Y (E ω / p n) ω)) Q)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂Q, 0 ≤ Y (E ω / p n) ω) :
    Tendsto
      (fun n : ℕ => ∫ ω, Real.exp (-β * Y (E ω / p n) ω) ∂Q)
      atTop
      (nhds (∫ ω, Real.exp (-β * Yinf ω) ∂Q)) := by
  refine esscher_infimum_bounded_laplace_convergence Q
    (fun n ω => Y (E ω / p n) ω) Yinf β hβ hmeas hpos ?_
  filter_upwards
    [esscher_shared_clock_pathwise_limit Q E Y Yinf hE hY]
    with ω hω
  exact hω.comp hp
