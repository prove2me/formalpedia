-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.misiurewicz_juliaSet_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:36.618949+00:00
-- url     : https://prove2.me/submissions/2f4756ee-f0ab-427b-8224-e25cf3fb5597

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_misiurewicz_fatouSet_exp

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution : juliaSet exponentialMap = Set.univ := by
  rw [juliaSet, misiurewicz_fatouSet_exp, Set.compl_empty]
end ExponentialJuliaSetMisiurewicz
