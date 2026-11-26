-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.noncentral_implies_global_parity_deviation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:03.017843+00:00
-- url     : https://prove2.me/submissions/a8c7ed82-3445-4384-82e4-5f8154ad28d2

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
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
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
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
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr

set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s K : ℕ} {eta : ℝ}
    (u : Fin M) (huK : (u : ℕ) < K)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 2 ≤ eta * M)
    (hnot : ¬ InCentralRenyiWindow (M - (u : ℕ)) s eta) :
    eta / 2 * M < |(s : ℝ) - (M : ℝ) / 2| := by
  unfold InCentralRenyiWindow at hnot
  have hcastSub :
      (((M - (u : ℕ) : ℕ) : ℝ)) = (M : ℝ) - (u : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt u.isLt)]
  have hfarNat :
      eta * (((M - (u : ℕ) : ℕ) : ℝ)) <
        |(s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2| :=
    lt_of_not_ge hnot
  have hfar :
      eta * ((M : ℝ) - (u : ℝ)) <
        |(s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2| := by
    simpa only [hcastSub] using hfarNat
  let a : ℝ :=
    (s : ℝ) - (((M - (u : ℕ) : ℕ) : ℝ) + 1) / 2
  let b : ℝ := (1 - (u : ℝ)) / 2
  let g : ℝ := (s : ℝ) - (M : ℝ) / 2
  have hga : g = a + b := by
    dsimp [g, a, b]
    rw [hcastSub]
    ring
  have hag : a = g - b := by linarith
  have hb : |b| ≤ ((u : ℝ) + 1) / 2 := by
    apply (abs_le).2
    dsimp [b]
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    constructor <;> nlinarith
  have htri : |a| ≤ |g| + |b| := by
    rw [hag]
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le g (-b)
  have huKR : (u : ℝ) < K := by exact_mod_cast huK
  have huBound : (u : ℝ) < eta * M / 8 := huKR.trans_le hK
  have hetaU : eta * (u : ℝ) ≤ (u : ℝ) / 2 := by
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    nlinarith
  have hfar' : eta * ((M : ℝ) - (u : ℝ)) < |a| := by
    simpa [a, hcastSub] using hfar
  dsimp [g] at htri ⊢
  nlinarith
end CollatzEndpointTransport.FixedTotal
