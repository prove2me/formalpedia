-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:19:32.951839+00:00
-- url     : https://prove2.me/submissions/fb5b081d-3cdd-4bb0-909c-68830faeb834

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 20000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {iota : Type*} (U : Finset iota) (p : iota → ℝ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hp : ∀ i ∈ U, 0 ≤ p i)
    (hpsum : ∑ i ∈ U, p i ≤ 1) :
    ∑ i ∈ U, (p i) ^ (1 - theta) ≤
      (U.card : ℝ) ^ theta := by
  by_cases hU : U = ∅
  · simp [hU, Real.zero_rpow htheta0.ne']
  have hcardNat : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
  have hcard : 0 < (U.card : ℝ) := Nat.cast_pos.mpr hcardNat
  let w : iota → ℝ := fun _ => (U.card : ℝ)⁻¹
  let q : iota → ℝ := fun i => (U.card : ℝ) * p i
  have hwsum : ∑ i ∈ U, w i = 1 := by
    simp [w, hcard.ne']
  have hw0 : ∀ i ∈ U, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hqmem : ∀ i ∈ U, q i ∈ Set.Ici (0 : ℝ) := by
    intro i hi
    exact Set.mem_Ici.mpr (mul_nonneg hcard.le (hp i hi))
  have hconc := Real.concaveOn_rpow
    (p := 1 - theta) (by linarith) (by linarith)
  have hj := hconc.le_map_sum hw0 hwsum hqmem
  have hleft :
      ∑ i ∈ U, w i • ((q i) ^ (1 - theta)) =
        (U.card : ℝ) ^ (-theta) *
          ∑ i ∈ U, (p i) ^ (1 - theta) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_eq_mul]
    dsimp [w, q]
    rw [Real.mul_rpow hcard.le (hp i hi)]
    rw [Real.rpow_one_sub' hcard.le (by linarith : 1 - theta ≠ 0)]
    rw [Real.rpow_neg hcard.le]
    field_simp [hcard.ne', (Real.rpow_pos_of_pos hcard _).ne']
  have hright :
      (∑ i ∈ U, w i • q i) ^ (1 - theta) ≤ 1 := by
    have hsumq : ∑ i ∈ U, w i • q i = ∑ i ∈ U, p i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [smul_eq_mul]
      dsimp [w, q]
      field_simp [hcard.ne']
    rw [hsumq]
    exact Real.rpow_le_one
      (Finset.sum_nonneg fun i hi => hp i hi)
      hpsum (by linarith)
  rw [hleft] at hj
  have hscaled :
      (U.card : ℝ) ^ (-theta) *
          ∑ i ∈ U, (p i) ^ (1 - theta) ≤ 1 :=
    hj.trans hright
  have hpowPos : 0 < (U.card : ℝ) ^ (-theta) :=
    Real.rpow_pos_of_pos hcard _
  have hdiv :
      ∑ i ∈ U, (p i) ^ (1 - theta) ≤
        1 / (U.card : ℝ) ^ (-theta) :=
    (le_div_iff₀ hpowPos).2 (by simpa [mul_comm] using hscaled)
  rw [one_div, ← Real.rpow_neg hcard.le] at hdiv
  simpa using hdiv
end CollatzEndpointTransport.FixedTotal
