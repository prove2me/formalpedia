-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:13.404562+00:00
-- url     : https://prove2.me/submissions/96e522b4-0033-4234-853f-8c5d6ffcaa8a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseMajorantAverage_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_le_reverseAverage
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta)
    (hcontract : 3 ^ s ≤ 2 ^ N) :
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta) *
        ((N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralSeparatorProportion N s)) + 2) := by
  have hcard : 0 < (fixedSet N s).card := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact Nat.choose_pos (by omega)
  have hbase := fixedRenyiMoment_le_reverseAverage
    htheta0 htheta1 hcard
  have havg := fixedReverseMajorantAverage_le
    htheta0 hN hs1 hsN hpiAlpha hcontract
  calc
    fixedRenyiMoment N s theta ≤
        4 * (((2 : ℝ) ^ N) ^ theta) *
          fixedReverseMajorantAverage N s theta /
            (((fixedSet N s).card : ℝ) ^ theta) := hbase
    _ ≤ 4 * (((2 : ℝ) ^ N) ^ theta) *
          ((N : ℝ) * (3 : ℝ) ^ (-theta) /
            (1 - centralRenyiRatio theta
              (centralSeparatorProportion N s)) + 2) /
            (((fixedSet N s).card : ℝ) ^ theta) := by
      gcongr
    _ = 4 * (((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta) *
        ((N : ℝ) * (3 : ℝ) ^ (-theta) /
          (1 - centralRenyiRatio theta
            (centralSeparatorProportion N s)) + 2) := by ring
end CollatzEndpointTransport.FixedTotal
