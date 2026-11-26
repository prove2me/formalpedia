-- Prove2me | solution 1 for FD1D.DyadicMass.cdf_sub_linear_eq_haar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:25.515839+00:00
-- url     : https://prove2.me/submissions/2e3eb494-e8e3-42c6-840d-618872ba15b9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z = q.haarSeries z := by
  induction q generalizing z with
  | leaf m => simp [piecewiseCDF, total, haarSeries]
  | @branch L l r ihl ihr =>
      by_cases hz : z ≤ 1 / 2
      · have h2z0 : 0 ≤ 2 * z := by linarith
        have h2z1 : 2 * z ≤ 1 := by linarith
        rw [piecewiseCDF, haarSeries]
        simp only [hz, if_pos]
        rw [← ihl h2z0 h2z1]
        rw [unitTent, if_pos hz]
        simp only [total]
        ring
      · have h2z0 : 0 ≤ 2 * z - 1 := by linarith
        have h2z1 : 2 * z - 1 ≤ 1 := by linarith
        rw [piecewiseCDF, haarSeries]
        simp only [hz, if_neg]
        rw [← ihr h2z0 h2z1]
        rw [unitTent, if_neg hz]
        simp only [total, if_false]
        ring
end FD1D.DyadicMass
