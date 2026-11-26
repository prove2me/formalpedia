-- Prove2me | solution 1 for FD1D.DyadicMass.haarSeries_eq_haarTermSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:39.936885+00:00
-- url     : https://prove2.me/submissions/553d491a-2e02-49d3-a795-8afda9456367

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_haarSeries_eq_haarTermSumAt
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
namespace DyadicMass
theorem _root_.solution
    {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z = haarTermSum q.haarTerms z := by
  simpa [DyadicMass.haarTerms] using
    q.haarSeries_eq_haarTermSumAt (a := 0) (p := 1) (z := z)
      (by norm_num) hz0 (by simpa using hz1)
end DyadicMass
end FD1D
