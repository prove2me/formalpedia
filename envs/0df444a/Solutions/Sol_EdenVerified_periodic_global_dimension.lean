-- Prove2me | solution 1 for EdenVerified.periodic_global_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:21.320933+00:00
-- url     : https://prove2.me/submissions/ac22d984-d90c-4c24-b4f8-a1d8aefa5f1e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_periodicGlobalGrowthDimension_eq_three
import Theorems.Thm_Eden_periodicGlobalGrowthIndex_eq_three
import Theorems.Thm_Eden_periodicGlobalGrowthInterpolation_isGreatest


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    kaplanYorkeIndex (periodicGlobalGrowthIncrements c) = 3 ∧
    IsGreatest {d : ℝ | d ∈ Icc 0 5 ∧ 0 ≤ periodicGlobalGrowthInterpolation c d} 3 ∧
    periodicGlobalGrowthDimension c = 3 :=
  ⟨periodicGlobalGrowthIndex_eq_three hc, periodicGlobalGrowthInterpolation_isGreatest hc,
    periodicGlobalGrowthDimension_eq_three hc⟩
end EdenVerified
