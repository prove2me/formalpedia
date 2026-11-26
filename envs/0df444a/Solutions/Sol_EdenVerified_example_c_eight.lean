-- Prove2me | solution 1 for EdenVerified.example_c_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:55:14.346443+00:00
-- url     : https://prove2.me/submissions/e60a1e7c-e9f9-423b-a07c-86ad6bf71e6c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
import Theorems.Thm_Eden_finiteTimeDimension_periodic_isGreatest
import Theorems.Thm_Eden_globalLyapunovDimension_attractor_eight


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
    IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
    (∀ t : ℝ, 0 < t →
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3) :=
  ⟨globalLyapunovDimension_attractor_eight,
    asymptoticDimension_periodic_isGreatest (by norm_num),
    fun t ht => finiteTimeDimension_periodic_isGreatest (by norm_num) ht⟩
end EdenVerified
