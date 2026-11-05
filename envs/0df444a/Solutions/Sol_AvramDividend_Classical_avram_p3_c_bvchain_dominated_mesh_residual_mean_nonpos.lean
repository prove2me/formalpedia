-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:23:33.321061+00:00
-- url     : https://prove2.me/submissions/a72fe530-aaba-4c11-b4bf-486fe58f40f4

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- A uniformly integrably dominated BV source-mesh residual retains its
nonpositive mean at an almost-everywhere limiting source residual. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ) (Efinal B : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (E n) P)
    (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, |E n ω| ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (nhds (Efinal ω)))
    (hMean : ∀ n, (∫ ω, E n ω ∂P) ≤ 0) :
    (∫ ω, Efinal ω ∂P) ≤ 0 := by
  have hConv := tendsto_integral_of_dominated_convergence
    B hMeas hB (by simpa only [Real.norm_eq_abs] using hBound) hLimit
  exact le_of_tendsto hConv (Filter.Eventually.of_forall hMean)
