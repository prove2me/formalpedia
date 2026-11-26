-- Prove2me | solution 1 for FD1D.DyadicMass.quantile_cost_within_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:05.512238+00:00
-- url     : https://prove2.me/submissions/d517ce6a-a865-4538-a10d-1390af6b70cc

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_MonotoneQuantilePolicy_expectedDistance_le

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
namespace DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    (q.quantilePolicy hq).expectedDistance ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea (fun z => q.piecewiseCDF z - z) := by
  exact (q.quantilePolicy hq).expectedDistance_le
end DyadicMass
end FD1D
