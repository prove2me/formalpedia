-- Prove2me | solution 1 for Eden.supremumSingularProduct_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:28.459912+00:00
-- url     : https://prove2.me/submissions/62e2d67b-94c0-4091-8a0c-1e632c9a9991

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_integerGrowthValues_nonempty
import Theorems.Thm_Eden_integerGrowthValues_bddAbove
import Theorems.Thm_Eden_attractor_nonempty
import Theorems.Thm_Eden_singularValueFunction_integer_evolution_bounds


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    Real.exp ((k : ℝ) * (-c * t)) ≤ supremumSingularProduct c k t ∧
      supremumSingularProduct c k t ≤ Real.exp ((k : ℝ) * (3 * t)) := by
  constructor
  · obtain ⟨p, hp⟩ := attractor_nonempty
    exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).1.trans
      (le_csSup (integerGrowthValues_bddAbove hk hc ht) ⟨p, hp, rfl⟩)
  · apply csSup_le (integerGrowthValues_nonempty c k t)
    rintro x ⟨p, hp, rfl⟩
    exact (singularValueFunction_integer_evolution_bounds hk hc ht hp).2
end Eden
