-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.numerator_div_global_le_card_mul_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:12.143806+00:00
-- url     : https://prove2.me/submissions/91414cee-fd9b-484f-8780-ac3e983d151e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiNumerator_nonneg
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



set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s B : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta)
    (hcard : 0 < (fixedSet N s).card)
    (hB : (fixedSet N s).card ≤ B) :
    fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
      ((fixedSet N s).card : ℝ) * fixedRenyiMoment N s theta := by
  let L : ℝ := (fixedSet N s).card
  have hL : 0 < L := Nat.cast_pos.mpr hcard
  have hBR : 0 < (B : ℝ) := by
    exact lt_of_lt_of_le hL (by simpa [L] using (Nat.cast_le.mpr hB :
      ((fixedSet N s).card : ℝ) ≤ (B : ℝ)))
  have hpow : L ^ theta ≤ (B : ℝ) ^ theta :=
    Real.rpow_le_rpow hL.le
      (by simpa [L] using (Nat.cast_le.mpr hB :
        ((fixedSet N s).card : ℝ) ≤ (B : ℝ))) htheta
  have hnum : 0 ≤ fixedRenyiNumerator N s theta :=
    fixedRenyiNumerator_nonneg N s theta
  unfold fixedRenyiMoment
  have hdiv :
      fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
        fixedRenyiNumerator N s theta / L ^ theta :=
    div_le_div_of_nonneg_left hnum (Real.rpow_pos_of_pos hL _) hpow
  calc
    fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
        fixedRenyiNumerator N s theta / L ^ theta := hdiv
    _ = L *
        (fixedRenyiNumerator N s theta / L ^ (1 + theta)) := by
      rw [Real.rpow_add hL]
      simp only [Real.rpow_one]
      field_simp [hL.ne', (Real.rpow_pos_of_pos hL _).ne']
end CollatzEndpointTransport.FixedTotal
