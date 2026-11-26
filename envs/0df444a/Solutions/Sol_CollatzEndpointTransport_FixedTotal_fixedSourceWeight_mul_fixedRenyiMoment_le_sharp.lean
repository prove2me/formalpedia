-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:19:04.911072+00:00
-- url     : https://prove2.me/submissions/6d22506c-df5b-47b3-bb10-13841028df71

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_piStar_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_uniform_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
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
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_eq
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
    {N s : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hcen : InCentralRenyiWindow N s eta)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
      centralMomentConstant theta eta * (N + 1) *
        (fixedSourceWeight N s) ^ (1 - theta) := by
  have hcard : 0 < (fixedSet N s).card := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact Nat.choose_pos (by omega)
  have hmoment := fixedRenyiMoment_central_uniform_le
    htheta0 htheta1 heta0 heta1 hN hs1 hsN hcen hsizePi hsizeDrift
  have hscale := source_weight_scale_eq hcard htheta1
  have hden : 0 < 1 -
      centralRenyiRatio theta (centralRenyiPiStar theta eta) := by
    linarith [centralRenyiRatio_piStar_lt_one
      htheta0 htheta1 heta0 heta1]
  let A := (3 : ℝ) ^ (-theta) /
    (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbracket :
      (N : ℝ) * A + 2 ≤ (N + 1 : ℝ) * (A + 2) := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have hp0 : 0 ≤ fixedSourceWeight N s :=
    fixedSourceWeight_nonneg N s
  have hbracket0 : 0 ≤ (N : ℝ) * A + 2 := by positivity
  calc
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        fixedSourceWeight N s *
          (4 * ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta)) *
            ((N : ℝ) * A + 2)) := by
      apply mul_le_mul_of_nonneg_left _ hp0
      exact hmoment.trans_eq (by
        dsimp [A]
        ring)
    _ = 4 *
          (fixedSourceWeight N s *
            ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta)) *
            ((N : ℝ) * A + 2)) := by ring
    _ ≤ 4 *
          ((fixedSourceWeight N s) ^ (1 - theta) *
            ((N + 1 : ℝ) * (A + 2))) := by
      rw [hscale]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbracket
          (Real.rpow_nonneg hp0 _)) (by norm_num)
    _ = centralMomentConstant theta eta * (N + 1) *
          (fixedSourceWeight N s) ^ (1 - theta) := by
      unfold centralMomentConstant
      dsimp [A]
      ring
end CollatzEndpointTransport.FixedTotal
