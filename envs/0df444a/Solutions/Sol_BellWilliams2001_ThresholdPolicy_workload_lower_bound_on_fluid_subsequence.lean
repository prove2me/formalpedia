-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.workload_lower_bound_on_fluid_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:07:38.172808+00:00
-- url     : https://prove2.me/submissions/b8429149-f1a5-4855-adf2-c62efc31aa57

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_input_coupling_after_fluid_allocation
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_discounted_lower_bound_from_workload_coupling

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hfluid : UocInProb M.P (fun n ω t => M.Tbar (φ n) (T (φ n)) ω t) M.fluidAllocation)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    M.Jstar P' B ≤ liminf (fun n => M.cost (φ n) (T (φ n))) atTop := by
  have hC := (workload_input_coupling_after_fluid_allocation M φ hφ.tendsto_atTop (T ∘ φ)
    (Eventually.of_forall fun n => hT (φ n)) hfluid Ω' P' B hB).1
  exact discounted_lower_bound_from_workload_coupling M T hT φ hφ.tendsto_atTop Ω' P' B hB hC
