-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulus_subset_tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:21.276799+00:00
-- url     : https://prove2.me/submissions/fed3c11c-0966-4ad4-babd-fd2d76f061cc

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialCenterDistance_le_half_add_one

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H j : ℕ} (_hj : 0 < j) :
    binomialAnnulus H j ⊆
      Finset.Ico 0 (binomialAnnulusCutoff H j + 1) ∪
        Finset.Ico (H - binomialAnnulusCutoff H j) (H + 1) := by
  intro k hk
  have hkData := (Finset.mem_filter.mp hk)
  have hkH : k ≤ H := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hkData.1)
  have hdistLower := hkData.2.1
  have hdistUpper := binomialCenterDistance_le_half_add_one hkH
  let W := binomialAnnulusWidth H
  let d := j * W
  have hdBound : d ≤ H / 2 + 1 := by
    simpa [d, W] using hdistLower.trans hdistUpper
  have htwoc : 2 * (H / 2) ≤ H := by
    simpa [mul_comm] using Nat.div_mul_le_self H 2
  have hHc : H ≤ 2 * (H / 2) + 1 := by omega
  rw [Finset.mem_union]
  by_cases hside : k ≤ H / 2
  · left
    rw [Finset.mem_Ico]
    constructor
    · omega
    · unfold binomialCenterDistance at hdistLower
      rw [if_pos hside] at hdistLower
      simp only [binomialAnnulusCutoff]
      omega
  · right
    rw [Finset.mem_Ico]
    constructor
    · unfold binomialCenterDistance at hdistLower
      rw [if_neg hside] at hdistLower
      simp only [binomialAnnulusCutoff]
      omega
    · omega
end CollatzEndpointTransport.FixedTotal
