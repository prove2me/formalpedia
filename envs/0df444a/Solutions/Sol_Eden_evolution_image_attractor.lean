-- Prove2me | solution 1 for Eden.evolution_image_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:03.159423+00:00
-- url     : https://prove2.me/submissions/392926b9-4100-4db8-8ed7-d5dc87c49b41

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
import Theorems.Thm_Eden_evolution_surjOn_attractor
import Theorems.Thm_Eden_evolution_mem_attractor


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' attractor = attractor := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact evolution_mem_attractor c ht hp
  · exact evolution_surjOn_attractor c ht
end Eden
