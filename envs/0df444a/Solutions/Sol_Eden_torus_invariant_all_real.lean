-- Prove2me | solution 1 for Eden.torus_invariant_all_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:42.710563+00:00
-- url     : https://prove2.me/submissions/19e63fb7-e2e5-4a86-bb22-6c7cfaa7ba84

import Definitions.Def_Eden_CircleOrbits
import Definitions.Def_Eden_TorusAngles
import Theorems.Thm_Eden_torusPoint_mem
import Theorems.Thm_Eden_exists_torusPoint_of_mem
import Theorems.Thm_Eden_evolution_torusPoint

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c t : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    evolution c t p ∈ torus := by
  obtain ⟨θ₁, θ₂, rfl⟩ := exists_torusPoint_of_mem hp
  rw [evolution_torusPoint]
  exact torusPoint_mem _ _
end Eden
