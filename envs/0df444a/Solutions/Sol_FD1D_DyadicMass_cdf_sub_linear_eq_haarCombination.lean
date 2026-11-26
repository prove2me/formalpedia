-- Prove2me | solution 1 for FD1D.DyadicMass.cdf_sub_linear_eq_haarCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:55.617844+00:00
-- url     : https://prove2.me/submissions/35fa3166-5cb7-4c07-9b9e-939c694d4d03

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_DyadicMass_cdf_sub_linear_eq_haar
import Theorems.Thm_FD1D_DyadicMass_haarSeries_eq_haarCombination

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by
  rw [q.cdf_sub_linear_eq_haar hz0 hz1,
    q.haarSeries_eq_haarCombination hz0 hz1]
end FD1D.DyadicMass
