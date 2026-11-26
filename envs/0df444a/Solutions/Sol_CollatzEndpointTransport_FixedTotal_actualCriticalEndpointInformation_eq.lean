-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualCriticalEndpointInformation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:27.009103+00:00
-- url     : https://prove2.me/submissions/a2dc7d40-889f-4267-9965-61720142a0c6

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelCriticalContribution_eq_level
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelCriticalContribution_zero

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) :
    actualCriticalEndpointInformation M =
      criticalEndpointInformation M := by
  unfold actualCriticalEndpointInformation criticalEndpointInformation
  congr 1
  rw [Finset.sum_range_succ']
  rw [actualLevelCriticalContribution_zero]
  have hsum :
      (∑ s ∈ Finset.range M,
          actualLevelCriticalContribution M (s + 1)) =
        ∑ s ∈ Finset.Icc 1 M,
          actualLevelCriticalContribution M s := by
    apply Finset.sum_bij
        (fun s hs => s + 1)
    · intro s hs
      rw [Finset.mem_Icc]
      exact ⟨by omega, by
        have := Finset.mem_range.mp hs
        omega⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      omega
    · intro s hs
      have hs' := Finset.mem_Icc.mp hs
      refine ⟨s - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro s hs
      rfl
  rw [hsum]
  have hlevels :
      (∑ s ∈ Finset.Icc 1 M,
          actualLevelCriticalContribution M s) =
        ∑ s ∈ Finset.Icc 1 M,
          levelCriticalContribution M s := by
    apply Finset.sum_congr rfl
    intro s hs
    exact actualLevelCriticalContribution_eq_level
      (Finset.mem_Icc.mp hs).1
  rw [hlevels]
  ring
end CollatzEndpointTransport.FixedTotal
