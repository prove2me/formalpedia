-- Prove2me | solution 1 for EdenVerified.s07_dimension_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:19.866003+00:00
-- url     : https://prove2.me/submissions/c1aa97d3-a67e-4756-bc42-87d081992838

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_dimH_attractor_lt_globalLyapunovDimension
import Theorems.Thm_Eden_dimH_torus_lt_finiteTimeDimension


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor ∧
    (∀ t : ℝ, 0 < t → ∀ p ∈ torus,
      (dimH torus).toReal < finiteTimeDimension c t p) :=
  ⟨dimH_attractor_lt_globalLyapunovDimension hc,
    fun t ht p hp => dimH_torus_lt_finiteTimeDimension hc ht hp⟩
end EdenVerified
