-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fixedCriticalContribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:18.232483+00:00
-- url     : https://prove2.me/submissions/965bfa77-2362-4146-9ac4-845b5ced2c74

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalContribution_eq_zero_of_lt_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalAverage_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (u : Fin M) :
    (∑ s ∈ Finset.Icc 1 M,
        fixedCriticalContribution (M - (u : ℕ)) s) ≤
      8 * (M - (u : ℕ)) * (2 ^ (M - (u : ℕ) - 1) : ℝ) := by
  let N := M - (u : ℕ)
  have hN : 0 < N := by dsimp [N]; omega
  have hNM : N ≤ M := by dsimp [N]; omega
  have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
    intro s hs
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hs).1,
        (Finset.mem_Icc.mp hs).2.trans hNM⟩
  have hsumEq :
      (∑ s ∈ Finset.Icc 1 M,
          fixedCriticalContribution N s) =
        ∑ s ∈ Finset.Icc 1 N,
          fixedCriticalContribution N s := by
    symm
    apply Finset.sum_subset hsubset
    intro s hsM hsNot
    have hsN : N < s := by
      have hsOne : 1 ≤ s := (Finset.mem_Icc.mp hsM).1
      by_contra hnot
      have hsLe : s ≤ N := Nat.le_of_not_gt hnot
      exact hsNot (Finset.mem_Icc.mpr ⟨hsOne, hsLe⟩)
    exact fixedCriticalContribution_eq_zero_of_lt_length hsN
  have hden : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have havg := fixedCriticalAverage_le N hN
  have hsumBound :
      (∑ s ∈ Finset.Icc 1 N,
          fixedCriticalContribution N s) ≤
        8 * N * (2 ^ (N - 1) : ℝ) := by
    apply (div_le_iff₀ hden).mp
    simpa [fixedCriticalAverage, mul_assoc] using havg
  simpa [N, hsumEq] using hsumBound
end CollatzEndpointTransport.FixedTotal
