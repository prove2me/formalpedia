-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_levelCriticalContribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:58.949301+00:00
-- url     : https://prove2.me/submissions/371423b9-5376-4f39-b03c-aba0475f42e2

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelCriticalContribution_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedCriticalContribution_le

set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) :
    (∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s) ≤
      Real.sqrt M * (8 * M * (2 ^ M : ℝ)) := by
  calc
    (∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s) ≤
        ∑ s ∈ Finset.Icc 1 M,
          Real.sqrt M *
            ∑ u : Fin M,
              fixedCriticalContribution (M - (u : ℕ)) s := by
      exact Finset.sum_le_sum fun s hs =>
        levelCriticalContribution_le M s
    _ = Real.sqrt M *
        ∑ u : Fin M, ∑ s ∈ Finset.Icc 1 M,
          fixedCriticalContribution (M - (u : ℕ)) s := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ Real.sqrt M *
        ∑ u : Fin M,
          (8 * (M - (u : ℕ)) *
            (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
      gcongr
      exact sum_fixedCriticalContribution_le M _
    _ ≤ Real.sqrt M * (8 * M * (2 ^ M : ℝ)) := by
      gcongr
      calc
        (∑ u : Fin M,
            ((8 : ℝ) * (M - (u : ℕ)) *
              (2 ^ (M - (u : ℕ) - 1) : ℝ))) ≤
            ∑ u : Fin M,
              ((8 : ℝ) * M *
                (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
          apply Finset.sum_le_sum
          intro u hu
          have huNonneg : (0 : ℝ) ≤ (u : ℕ) := by positivity
          have hfactor :
              (0 : ℝ) ≤ 2 ^ (M - (u : ℕ) - 1) := by positivity
          nlinarith
        _ = (8 : ℝ) * M *
            (∑ u : Fin M,
              (2 ^ (M - (u : ℕ) - 1) : ℝ)) := by
          rw [Finset.mul_sum]
        _ ≤ (8 : ℝ) * M * (2 ^ M : ℝ) := by
          gcongr
          have hgeom := one_add_reverse_pow_sum M
          exact_mod_cast (by omega :
            (∑ u : Fin M, 2 ^ (M - (u : ℕ) - 1)) ≤ 2 ^ M)
end CollatzEndpointTransport.FixedTotal
