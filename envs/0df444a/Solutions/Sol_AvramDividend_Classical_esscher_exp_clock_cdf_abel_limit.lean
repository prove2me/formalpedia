-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_clock_cdf_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:32:19.467397+00:00
-- url     : https://prove2.me/submissions/5fdc67fd-dfe7-414f-8e26-142583d757fd

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_esscher_shared_clock_pathwise_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set

/-- Any positive common clock asymptotically samples the limiting CDF value. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (E : Ω → ℝ) (hE : ∀ᵐ ω ∂Q, 0 < E ω)
    (f : ℝ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => f (E ω / p n)) Q)
    (hbound : ∀ n : ℕ,
      ∀ᵐ ω ∂Q, ‖f (E ω / p n)‖ ≤ (1 : ℝ)) :
    Tendsto (fun n : ℕ => ∫ ω, f (E ω / p n) ∂Q)
      atTop (nhds L) := by
  have hconst :
      ∀ᵐ ω ∂Q, Tendsto (fun t : ℝ => f t) atTop (nhds L) :=
    Filter.Eventually.of_forall (fun _ => hf)
  have hlimit :
      ∀ᵐ ω ∂Q,
        Tendsto (fun n : ℕ => f (E ω / p n)) atTop (nhds L) := by
    filter_upwards
      [esscher_shared_clock_pathwise_limit Q E
        (fun t (_ : Ω) => f t) (fun _ => L) hE hconst]
      with ω hω
    exact hω.comp hp
  have hInt := tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ)) hmeas (integrable_const _) hbound hlimit
  simpa using hInt
