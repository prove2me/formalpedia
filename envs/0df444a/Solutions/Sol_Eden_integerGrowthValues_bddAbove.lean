-- Prove2me | solution 1 for Eden.integerGrowthValues_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:16.174318+00:00
-- url     : https://prove2.me/submissions/730f5f10-7611-4180-a2af-ec638bea9e0d

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_singularValueFunction_integer_evolution_bounds


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : BddAbove (integerGrowthValues c k t) := by
  refine ⟨Real.exp ((k : ℝ) * (3 * t)), ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).2
end Eden
