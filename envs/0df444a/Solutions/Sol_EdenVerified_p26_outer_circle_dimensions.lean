-- Prove2me | solution 1 for EdenVerified.p26_outer_circle_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:10.972443+00:00
-- url     : https://prove2.me/submissions/eefd5d8d-0d9f-46fb-93d3-ab7bc9fe1233

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_first_outer_circle
import Theorems.Thm_Eden_asymptoticDimension_second_outer_circle
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
import Theorems.Thm_Eden_normalizedLogSingularValues_outer_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2) :
    finiteTimeDimension c t p = 1 ∧ asymptoticDimension c p = 1 := by
  constructor
  · rw [finiteTimeDimension_eq_kaplanYorke c ht p,
      normalizedLogSingularValues_outer_circle hc ht hp, kaplanYorkeDimension_zero_two hc]
  · rcases hp with hp | hp
    · exact asymptoticDimension_first_outer_circle hc hp
    · exact asymptoticDimension_second_outer_circle hc hp
end EdenVerified
