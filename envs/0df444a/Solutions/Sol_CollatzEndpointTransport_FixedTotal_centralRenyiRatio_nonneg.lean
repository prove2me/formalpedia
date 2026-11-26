-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:19.611531+00:00
-- url     : https://prove2.me/submissions/c1198609-e5b4-4edb-a986-f05f4665a1cc

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 ≤ pi) :
    0 ≤ centralRenyiRatio theta pi := by
  unfold centralRenyiRatio
  have hden : 0 < (2 : ℝ) ^ theta - 1 + pi := by
    linarith [one_lt_two_rpow htheta]
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hpi)
    hden.le
end CollatzEndpointTransport.FixedTotal
