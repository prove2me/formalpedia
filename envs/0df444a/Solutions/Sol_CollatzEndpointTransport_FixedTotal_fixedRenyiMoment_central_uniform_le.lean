-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_uniform_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:01.598672+00:00
-- url     : https://prove2.me/submissions/bf7b2bfc-8f72-411a-9e6b-a5dbe5fe8152

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSeparatorProportion_le_piStar
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_le_log_ratio
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_le_two_pow_of_cast_le_log_ratio
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_lt_alpha
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_mono
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_piStar_lt_one


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
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
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta) *
        ((N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralRenyiPiStar theta eta)) + 2) := by
  have hpi := centralSeparatorProportion_le_piStar hN (by omega) hcen hsizePi
  have hpi0 : 0 < centralSeparatorProportion N s := by
    unfold centralSeparatorProportion
    exact div_pos (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hs1))
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hN))
  have hpiAlpha := hpi.trans_lt (centralRenyiPiStar_lt_alpha heta1)
  have hcontract := three_pow_le_two_pow_of_cast_le_log_ratio
    (central_window_le_log_ratio hcen hsizeDrift)
  have hbase := fixedRenyiMoment_central_le htheta0 htheta1.le
    hN hs1 hsN hpiAlpha hcontract
  have hratio := centralRenyiRatio_mono htheta0 hpi0.le hpi
  have hstarlt := centralRenyiRatio_piStar_lt_one
    htheta0 htheta1
    heta0 heta1
  have hden0 : 0 < 1 - centralRenyiRatio theta
      (centralSeparatorProportion N s) := by
    linarith [centralRenyiRatio_lt_one htheta0 hpi0 hpiAlpha]
  have hdenStar : 0 < 1 - centralRenyiRatio theta
      (centralRenyiPiStar theta eta) := by linarith
  have hdenLe :
      1 - centralRenyiRatio theta (centralRenyiPiStar theta eta) ≤
        1 - centralRenyiRatio theta
          (centralSeparatorProportion N s) := by
    linarith
  have hfrac :
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralSeparatorProportion N s)) ≤
        (N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralRenyiPiStar theta eta)) := by
    exact div_le_div_of_nonneg_left (by positivity) hdenStar hdenLe
  calc
    fixedRenyiMoment N s theta ≤
        4 * (((2 : ℝ) ^ N) ^ theta) /
            (((fixedSet N s).card : ℝ) ^ theta) *
          ((N : ℝ) * (3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta
              (centralSeparatorProportion N s)) + 2) := hbase
    _ ≤ 4 * (((2 : ℝ) ^ N) ^ theta) /
            (((fixedSet N s).card : ℝ) ^ theta) *
          ((N : ℝ) * (3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta
              (centralRenyiPiStar theta eta)) + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end CollatzEndpointTransport.FixedTotal
