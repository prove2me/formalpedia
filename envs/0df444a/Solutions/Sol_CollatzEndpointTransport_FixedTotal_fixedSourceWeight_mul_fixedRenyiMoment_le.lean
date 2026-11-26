-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:53:27.288226+00:00
-- url     : https://prove2.me/submissions/60bfb5e6-3773-4864-abe0-748bcda9f1a0

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_uniform_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_le_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_piStar_lt_one
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


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

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
      centralMomentConstant theta eta * (N + 1) := by
  have hcard : 0 < (fixedSet N s).card := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact Nat.choose_pos (by omega)
  have hmoment := fixedRenyiMoment_central_uniform_le
    htheta0 htheta1 heta0 heta1 hN hs1 hsN hcen hsizePi hsizeDrift
  have hscale := source_weight_scale_le_one hcard htheta0 htheta1
  have hA0 : 0 ≤ (3 : ℝ) ^ (-theta) /
      (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) := by
    have hratio := centralRenyiRatio_piStar_lt_one
      htheta0 htheta1 heta0 heta1
    exact div_nonneg (by positivity) (by linarith)
  have hA :
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2 ≤
        (N + 1 : ℝ) *
          ((3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2) := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    calc
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2 =
          (N : ℝ) *
            ((3 : ℝ) ^ (-theta) /
              (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta))) + 2 := by
        ring
      _ ≤ ((N : ℝ) + 1) *
          ((3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2) := by
        nlinarith
      _ = (N + 1 : ℝ) *
          ((3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta (centralRenyiPiStar theta eta)) + 2) := by
        push_cast
        ring
  calc
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        fixedSourceWeight N s *
          (4 * ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta)) *
            ((N : ℝ) * (3 : ℝ) ^ (-theta) /
              (1 - centralRenyiRatio theta
                (centralRenyiPiStar theta eta)) + 2)) := by
      simpa only [div_eq_mul_inv, mul_assoc] using
        (mul_le_mul_of_nonneg_left hmoment
          (fixedSourceWeight_nonneg N s))
    _ ≤ 4 *
          ((N + 1 : ℝ) *
            ((3 : ℝ) ^ (-theta) /
              (1 - centralRenyiRatio theta
                (centralRenyiPiStar theta eta)) + 2)) := by
      have hfactor :
          fixedSourceWeight N s *
              ((((2 : ℝ) ^ N) ^ theta) /
                (((fixedSet N s).card : ℝ) ^ theta)) *
            ((N : ℝ) * (3 : ℝ) ^ (-theta) /
              (1 - centralRenyiRatio theta
                (centralRenyiPiStar theta eta)) + 2) ≤
          1 * ((N + 1 : ℝ) *
            ((3 : ℝ) ^ (-theta) /
              (1 - centralRenyiRatio theta
                (centralRenyiPiStar theta eta)) + 2)) := by
        have hcurrent :
            0 ≤ (N : ℝ) * (3 : ℝ) ^ (-theta) /
                (1 - centralRenyiRatio theta
                  (centralRenyiPiStar theta eta)) + 2 := by
          have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
          rw [show
            (N : ℝ) * (3 : ℝ) ^ (-theta) /
                (1 - centralRenyiRatio theta
                  (centralRenyiPiStar theta eta)) =
              (N : ℝ) *
                ((3 : ℝ) ^ (-theta) /
                  (1 - centralRenyiRatio theta
                    (centralRenyiPiStar theta eta))) by ring]
          nlinarith
        exact mul_le_mul hscale hA hcurrent zero_le_one
      nlinarith
    _ = centralMomentConstant theta eta * (N + 1) := by
      unfold centralMomentConstant
      push_cast
      ring
end CollatzEndpointTransport.FixedTotal
