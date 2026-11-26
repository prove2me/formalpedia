-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedCriticalAverage_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:57.970336+00:00
-- url     : https://prove2.me/submissions/c8f08e33-4858-459c-803a-abebeb7a555f

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalContribution_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_aggregateQ_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    fixedCriticalAverage N ≤ 8 * N := by
  let I := Finset.Icc 1 N
  let Y : ℕ → ℕ := fun s =>
    ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)
  have hterm :
      ∑ s ∈ I, fixedCriticalContribution N s ≤
        4 * ∑ s ∈ I, Real.sqrt (Y s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    simpa [Y] using fixedCriticalContribution_le N s
  have hcardI : I.card = N := by
    simp [I, Nat.card_Icc]
  have hcs :
      (∑ s ∈ I, Real.sqrt (Y s)) ^ 2 ≤
        (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := by
    have hraw :=
      (sq_sum_le_card_mul_sum_sq
        (s := I) (f := fun s => Real.sqrt (Y s)))
    rw [hcardI] at hraw
    calc
      (∑ s ∈ I, Real.sqrt (Y s)) ^ 2
          ≤ (N : ℝ) * ∑ s ∈ I, (Real.sqrt (Y s)) ^ 2 := hraw
      _ = (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := by
        apply congrArg (fun z : ℝ => (N : ℝ) * z)
        apply Finset.sum_congr rfl
        intro s hs
        exact Real.sq_sqrt (by positivity)
  have hY :
      ∑ s ∈ I, Y s ≤ 4 * N * 4 ^ (N - 1) := by
    exact aggregateQ_le N hN
  have hYReal :
      (∑ s ∈ I, (Y s : ℝ)) ≤
        (4 * N * 4 ^ (N - 1) : ℕ) := by
    exact_mod_cast hY
  have hsumSqrt :
      ∑ s ∈ I, Real.sqrt (Y s) ≤
        2 * N * Real.sqrt (4 ^ (N - 1) : ℕ) := by
    have hnonneg :
        0 ≤ ∑ s ∈ I, Real.sqrt (Y s) := by positivity
    have hrhsNonneg :
        0 ≤ 2 * (N : ℝ) * Real.sqrt (4 ^ (N - 1) : ℕ) := by
      positivity
    have hsq :
        (∑ s ∈ I, Real.sqrt (Y s)) ^ 2 ≤
          (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) ^ 2 := by
      calc
        (∑ s ∈ I, Real.sqrt (Y s)) ^ 2
            ≤ (N : ℝ) * ∑ s ∈ I, (Y s : ℝ) := hcs
        _ ≤ (N : ℝ) * (4 * N * 4 ^ (N - 1) : ℕ) := by
          gcongr
        _ = (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) ^ 2 := by
          rw [mul_pow]
          rw [Real.sq_sqrt (by positivity)]
          norm_num
          ring
    nlinarith
  have hpowPos : (0 : ℝ) < 2 ^ (N - 1) := by positivity
  have hsqrtPow :
      Real.sqrt (4 ^ (N - 1) : ℕ) = (2 ^ (N - 1) : ℝ) := by
    have hpowNat :
        4 ^ (N - 1) = (2 ^ (N - 1)) ^ 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hpowNat]
    rw [Nat.cast_pow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    norm_num [Nat.cast_pow]
  apply (div_le_iff₀ hpowPos).2
  change
    (∑ s ∈ I, fixedCriticalContribution N s) ≤
      8 * N * (2 ^ (N - 1) : ℝ)
  calc
    (∑ s ∈ I, fixedCriticalContribution N s)
        ≤ 4 * ∑ s ∈ I, Real.sqrt (Y s) := hterm
    _ ≤ 4 * (2 * N * Real.sqrt (4 ^ (N - 1) : ℕ)) := by
      gcongr
    _ = 8 * N * (2 ^ (N - 1) : ℝ) := by rw [hsqrtPow]; ring
end CollatzEndpointTransport.FixedTotal
