-- Prove2me | solution 1 for EdenVerified.p26_unit_circle_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:02.604651+00:00
-- url     : https://prove2.me/submissions/b78f1b34-6785-4a8d-ae66-c7184917c267

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_first_unit_circle
import Theorems.Thm_Eden_asymptoticDimension_second_unit_circle
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_normalizedLogSingularValues_unit_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (t : ℝ) (ht : 0 < t)
    (p : PhaseSpace) (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1) :
    finiteTimeDimension c t p = 3 ∧ asymptoticDimension c p = 3 := by
  constructor
  · rw [finiteTimeDimension_eq_kaplanYorke c ht p,
      normalizedLogSingularValues_unit_circle hc ht hp, kaplanYorkeDimension_zero_one hc]
  · rcases hp with hp | hp
    · exact asymptoticDimension_first_unit_circle hc hp
    · exact asymptoticDimension_second_unit_circle hc hp
end EdenVerified
