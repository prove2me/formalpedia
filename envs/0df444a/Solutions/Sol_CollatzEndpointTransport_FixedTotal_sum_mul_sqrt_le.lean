-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_mul_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:39.611148+00:00
-- url     : https://prove2.me/submissions/2aeef2b8-7042-4347-813d-69309924513a

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mul_sqrt_eq_rpow_three_halves

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} (U : Finset ι) (a : ι → ℕ) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) *
        Real.sqrt (∑ i ∈ U, a i : ℕ) ≤
      Real.sqrt U.card *
        ∑ i ∈ U, (a i : ℝ) * Real.sqrt (a i) := by
  have hpow :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := U) (f := fun i => (a i : ℝ))
      (p := (3 : ℝ) / 2) (by norm_num)
      (by intro i hi; positivity)
  have hsumNonneg :
      0 ≤ ∑ i ∈ U, (a i : ℝ) := by positivity
  have hcardNonneg : (0 : ℝ) ≤ U.card := by positivity
  calc
    ((∑ i ∈ U, a i : ℕ) : ℝ) *
          Real.sqrt (∑ i ∈ U, a i : ℕ) =
        (∑ i ∈ U, (a i : ℝ)) *
          Real.sqrt (∑ i ∈ U, (a i : ℝ)) := by
      norm_num
    _ = (∑ i ∈ U, (a i : ℝ)) ^ ((3 : ℝ) / 2) :=
      mul_sqrt_eq_rpow_three_halves _ hsumNonneg
    _ ≤ (U.card : ℝ) ^ ((3 : ℝ) / 2 - 1) *
          ∑ i ∈ U, (a i : ℝ) ^ ((3 : ℝ) / 2) := hpow
    _ = Real.sqrt U.card *
          ∑ i ∈ U, (a i : ℝ) * Real.sqrt (a i) := by
      have hhalf : (3 : ℝ) / 2 - 1 = 1 / 2 := by norm_num
      rw [hhalf, ← Real.sqrt_eq_rpow]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (mul_sqrt_eq_rpow_three_halves (a i) (by positivity)).symm
end CollatzEndpointTransport.FixedTotal
