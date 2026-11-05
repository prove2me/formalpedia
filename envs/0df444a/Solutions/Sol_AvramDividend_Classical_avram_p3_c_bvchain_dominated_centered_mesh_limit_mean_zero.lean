-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_dominated_centered_mesh_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:32:10.214843+00:00
-- url     : https://prove2.me/submissions/1d6560b2-67f0-4fe2-8bf9-847e8b2f5c36

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.Hausdorff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- A dominated a.e. limit of integrable centered source-mesh terms stays centered. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℝ) (Mfinal B : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (M n) P)
    (hB : Integrable B P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, |M n ω| ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (nhds (Mfinal ω)))
    (hMean : ∀ n, (∫ ω, M n ω ∂P) = 0) :
    (∫ ω, Mfinal ω ∂P) = 0 := by
  have hConv := tendsto_integral_of_dominated_convergence
    B hMeas hB (by simpa only [Real.norm_eq_abs] using hBound) hLimit
  have hSeq :
      (fun n : ℕ => (∫ ω, M n ω ∂P)) = (fun _ => (0 : ℝ)) :=
    funext hMean
  rw [hSeq] at hConv
  exact tendsto_nhds_unique hConv tendsto_const_nhds
