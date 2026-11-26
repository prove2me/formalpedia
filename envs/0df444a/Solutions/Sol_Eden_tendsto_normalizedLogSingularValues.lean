-- Prove2me | solution 1 for Eden.tendsto_normalizedLogSingularValues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:18.708517+00:00
-- url     : https://prove2.me/submissions/022fc55c-57aa-4180-88bb-89d6e81114c2

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending
import Theorems.Thm_Eden_tendsto_descending
import Theorems.Thm_Eden_tendsto_log_derivativeFactors_div


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) := by
  apply (tendsto_descending (tendsto_log_derivativeFactors_div c p)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (normalizedLogSingularValues_eq_descending c ht p).symm
end Eden
