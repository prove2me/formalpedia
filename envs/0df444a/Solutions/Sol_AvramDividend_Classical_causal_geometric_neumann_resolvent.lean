-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_neumann_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:21:27.937987+00:00
-- url     : https://prove2.me/submissions/7b802f95-0a44-4ced-b2d6-102e0277ddd2

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_dominated_convergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_neumann_partial_sum_aestronglymeasurable
import Theorems.Thm_AvramDividend_Classical_causal_local_neumann_convolution_majorant
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_local_sum_bound
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_summable
import Theorems.Thm_AvramDividend_Classical_causal_neumann_tsum_partial_sum_tendsto
open AvramDividend.Classical MeasureTheory Set Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Geometric Neumann bounds provide every hypothesis for causal dominated convergence. -/
theorem solution
    (a ρ : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hB : ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume)
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hGeom : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x, ‖Q n s‖ ≤ C * ρ ^ n)
    (hPoint : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n)
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by
  have hI := causal_neumann_product_integrable B Q hB hMeas
    (fun x i => by
      obtain ⟨C, hC, h⟩ := hGeom x
      exact ⟨C * ρ ^ i, fun s hs => h i s hs⟩)
  have hSums : ∀ x : ℝ, Summable (fun n : ℕ => Q n x) := by
    intro x
    exact causal_geometric_neumann_summable Q ρ x hρ0 hρ1 (hPoint x)
  have hS := causal_neumann_tsum_partial_sum_tendsto Q g hSums hg
  have hQlimit : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ)) := by
    intro x
    exact (hSums x).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hProdMeas :=
    causal_neumann_partial_sum_aestronglymeasurable B Q hI
  have hSumBound :=
    causal_geometric_neumann_local_sum_bound Q ρ hρ0 hρ1 hGeom
  have hDom :=
    causal_local_neumann_convolution_majorant B Q hB hSumBound
  exact causal_neumann_resolvent_dominated_convergence a B F g Q
    hzero hstep hI hS hQlimit hProdMeas hDom
