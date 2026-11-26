-- Prove2me | solution 1 for FD1D.DyadicMass.quantile_discrepancy_eq_haar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:06.118605+00:00
-- url     : https://prove2.me/submissions/87f66b4c-91c9-4b77-9c33-301f62148d68

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_cdf_sub_linear_eq_haar
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace FD1D
namespace DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    q.piecewiseCDF z - z = q.haarSeries z := by
  simpa [hq.total_eq_one] using q.cdf_sub_linear_eq_haar hz.1 hz.2
end DyadicMass
end FD1D
