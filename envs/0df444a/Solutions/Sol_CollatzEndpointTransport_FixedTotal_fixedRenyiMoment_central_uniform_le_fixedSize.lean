-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:48:28.673056+00:00
-- url     : https://prove2.me/submissions/09196e88-1fd8-4ece-9c1b-73a6a1fafb8d

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseMajorantAverage_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_lt_alpha
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSeparatorProportion_le_piStar
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_le_log_ratio
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_le_reverseAverage
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_le_two_pow_of_cast_le_log_ratio
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
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hcen : InCentralRenyiWindow N s eta)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    fixedRenyiMoment N s theta ≤
      fixedSizeCentralMomentConstant theta eta *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) := by
  have hpi := centralSeparatorProportion_le_piStar
    (by omega : 1 < N) (by omega : 0 < s) hcen hsizePi
  have hpi0 : 0 < centralSeparatorProportion N s := by
    unfold centralSeparatorProportion
    exact div_pos
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hs1))
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (by omega : 1 < N)))
  have hpiAlpha := hpi.trans_lt (centralRenyiPiStar_lt_alpha heta1)
  have hcontract := three_pow_le_two_pow_of_cast_le_log_ratio
    (central_window_le_log_ratio hcen hsizeDrift)
  have hcard : 0 < (fixedSet N s).card := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact Nat.choose_pos (by omega)
  have hbase := fixedRenyiMoment_le_reverseAverage
    htheta0 htheta1.le hcard
  have havg := fixedReverseMajorantAverage_le_fixedSize
    htheta0 hN hs1 hsN hpiAlpha hcontract
  let B := (2 : ℝ) ^ theta - 1
  let G := (3 : ℝ) ^ theta - 1
  let pi := centralSeparatorProportion N s
  let star := centralRenyiPiStar theta eta
  have hB0 : 0 < B := by
    dsimp [B]
    linarith [one_lt_two_rpow htheta0]
  have hG0 : 0 < G := by
    dsimp [G]
    exact centralRenyiAlpha_den_pos htheta0
  have hdenPi : 0 < B - pi * G := by
    have hscaled : pi * G < B := by
      dsimp [pi, B, G]
      unfold centralRenyiAlpha at hpiAlpha
      simpa [mul_comm] using (lt_div_iff₀
        (centralRenyiAlpha_den_pos htheta0)).mp hpiAlpha
    linarith
  have hdenStar : 0 < B - star * G := by
    have hstarAlpha := centralRenyiPiStar_lt_alpha heta1
    have hscaled : star * G < B := by
      dsimp [star, B, G]
      unfold centralRenyiAlpha at hstarAlpha
      simpa [mul_comm] using (lt_div_iff₀
        (centralRenyiAlpha_den_pos htheta0)).mp hstarAlpha
    linarith
  have hfrac : pi / (B - pi * G) ≤ star / (B - star * G) := by
    rw [div_le_div_iff₀ hdenPi hdenStar]
    have hpistar : pi ≤ star := by simpa [pi, star] using hpi
    nlinarith [mul_nonneg hB0.le (sub_nonneg.mpr hpistar)]
  have hscale0 :
      0 ≤ (((2 : ℝ) ^ N) ^ theta) /
        (((fixedSet N s).card : ℝ) ^ theta) := by positivity
  calc
    fixedRenyiMoment N s theta ≤
        4 * (((2 : ℝ) ^ N) ^ theta) *
          fixedReverseMajorantAverage N s theta /
            (((fixedSet N s).card : ℝ) ^ theta) := hbase
    _ ≤ 4 * (((2 : ℝ) ^ N) ^ theta) *
          (pi / (B - pi * G) + 2) /
            (((fixedSet N s).card : ℝ) ^ theta) := by
      gcongr
    _ ≤ 4 * (((2 : ℝ) ^ N) ^ theta) *
          (star / (B - star * G) + 2) /
            (((fixedSet N s).card : ℝ) ^ theta) := by
      have hfourScale : 0 ≤
          4 * ((((2 : ℝ) ^ N) ^ theta) /
            (((fixedSet N s).card : ℝ) ^ theta)) := by positivity
      calc
        4 * (((2 : ℝ) ^ N) ^ theta) *
            (pi / (B - pi * G) + 2) /
              (((fixedSet N s).card : ℝ) ^ theta) =
            (4 * ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta))) *
              (pi / (B - pi * G) + 2) := by ring
        _ ≤ (4 * ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta))) *
              (star / (B - star * G) + 2) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hfourScale
        _ = 4 * (((2 : ℝ) ^ N) ^ theta) *
            (star / (B - star * G) + 2) /
              (((fixedSet N s).card : ℝ) ^ theta) := by ring
    _ = fixedSizeCentralMomentConstant theta eta *
          ((((2 : ℝ) ^ N) ^ theta) /
            (((fixedSet N s).card : ℝ) ^ theta)) := by
      unfold fixedSizeCentralMomentConstant
      dsimp [star, B, G]
      ring
end CollatzEndpointTransport.FixedTotal
