-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_weight_mul_rpow_mul_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:03.449784+00:00
-- url     : https://prove2.me/submissions/c422cff1-abd4-4cd2-82b3-566541a66e87

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
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
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} (U : Finset ι) (w a b : ι → ℝ)
    {theta : ℝ} (htheta : 0 < theta)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∑ i ∈ U,
        w i * (a i) ^ (theta / (1 + theta)) *
          (b i) ^ (1 / (1 + theta)) ≤
      (∑ i ∈ U, w i * a i) ^ (theta / (1 + theta)) *
        (∑ i ∈ U, w i * b i) ^ (1 / (1 + theta)) := by
  let p := (1 + theta) / theta
  let q := 1 + theta
  have hq : 0 < q := by dsimp [q]; linarith
  have hp : 1 < p := by
    dsimp [p]
    rw [lt_div_iff₀ htheta]
    linarith
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    dsimp [p, q]
    field_simp [htheta.ne', hq.ne']
    ring
  let f : ι → ℝ := fun i => (w i * a i) ^ (theta / (1 + theta))
  let g : ι → ℝ := fun i => (w i * b i) ^ (1 / (1 + theta))
  have hf : ∀ i ∈ U, 0 ≤ f i := by
    intro i hi
    exact Real.rpow_nonneg (mul_nonneg (hw i) (ha i)) _
  have hg : ∀ i ∈ U, 0 ≤ g i := by
    intro i hi
    exact Real.rpow_nonneg (mul_nonneg (hw i) (hb i)) _
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := U) (f := f) (g := g) hpq hf hg
  have hfpow : ∀ i ∈ U, (f i) ^ p = w i * a i := by
    intro i hi
    dsimp [f, p]
    rw [← Real.rpow_mul (mul_nonneg (hw i) (ha i))]
    have hthetaOne : 1 + theta ≠ 0 := hq.ne'
    have hexp : theta / (1 + theta) * ((1 + theta) / theta) = 1 := by
      field_simp [htheta.ne', hthetaOne]
    rw [hexp, Real.rpow_one]
  have hgpow : ∀ i ∈ U, (g i) ^ q = w i * b i := by
    intro i hi
    dsimp [g, q]
    rw [← Real.rpow_mul (mul_nonneg (hw i) (hb i))]
    have hexp : 1 / (1 + theta) * (1 + theta) = 1 := by
      field_simp [hq.ne']
    rw [hexp, Real.rpow_one]
  have hproduct : ∀ i ∈ U,
      f i * g i =
        w i * (a i) ^ (theta / (1 + theta)) *
          (b i) ^ (1 / (1 + theta)) := by
    intro i hi
    dsimp [f, g]
    rw [Real.mul_rpow (hw i) (ha i), Real.mul_rpow (hw i) (hb i)]
    have hsum : theta / (1 + theta) + 1 / (1 + theta) = 1 := by
      field_simp [hq.ne']
      ring
    calc
      w i ^ (theta / (1 + theta)) * a i ^ (theta / (1 + theta)) *
          (w i ^ (1 / (1 + theta)) * b i ^ (1 / (1 + theta))) =
          (w i ^ (theta / (1 + theta)) *
            w i ^ (1 / (1 + theta))) *
              a i ^ (theta / (1 + theta)) *
                b i ^ (1 / (1 + theta)) := by ring
      _ = w i ^ (theta / (1 + theta) + 1 / (1 + theta)) *
              a i ^ (theta / (1 + theta)) *
                b i ^ (1 / (1 + theta)) := by
            rw [Real.rpow_add_of_nonneg (hw i) (by positivity) (by positivity)]
      _ = w i * a i ^ (theta / (1 + theta)) *
              b i ^ (1 / (1 + theta)) := by
            rw [hsum, Real.rpow_one]
  calc
    ∑ i ∈ U,
        w i * (a i) ^ (theta / (1 + theta)) *
          (b i) ^ (1 / (1 + theta)) =
        ∑ i ∈ U, f i * g i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hproduct i hi).symm
    _ ≤ (∑ i ∈ U, (f i) ^ p) ^ (1 / p) *
          (∑ i ∈ U, (g i) ^ q) ^ (1 / q) := hholder
    _ = (∑ i ∈ U, w i * a i) ^ (theta / (1 + theta)) *
          (∑ i ∈ U, w i * b i) ^ (1 / (1 + theta)) := by
      have hfsum : ∑ i ∈ U, (f i) ^ p = ∑ i ∈ U, w i * a i := by
        apply Finset.sum_congr rfl
        exact hfpow
      have hgsum : ∑ i ∈ U, (g i) ^ q = ∑ i ∈ U, w i * b i := by
        apply Finset.sum_congr rfl
        exact hgpow
      rw [hfsum, hgsum]
      dsimp [p, q]
      have hexp : 1 / ((1 + theta) / theta) = theta / (1 + theta) := by
        field_simp [htheta.ne', hq.ne']
      rw [hexp]
end CollatzEndpointTransport.FixedTotal
