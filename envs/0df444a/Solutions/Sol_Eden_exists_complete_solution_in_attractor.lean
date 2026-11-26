-- Prove2me | solution 1 for Eden.exists_complete_solution_in_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:03.548363+00:00
-- url     : https://prove2.me/submissions/75f5c676-428c-4634-9eb0-425e4b7a1b94

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
import Theorems.Thm_Eden_hasDerivAt_evolution_of_mem_attractor
import Theorems.Thm_Eden_evolution_mem_attractor_all_time
import Theorems.Thm_Eden_evolution_zero_time
attribute [local simp] Eden.evolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ attractor) :
    ∃ f : ℝ → PhaseSpace, f 0 = p ∧ ∀ t : ℝ,
      f t ∈ attractor ∧ HasDerivAt f (vectorField c (f t)) t :=
  ⟨fun t => evolution c t p, evolution_zero_time c p, fun t =>
    ⟨evolution_mem_attractor_all_time c t hp, hasDerivAt_evolution_of_mem_attractor c t hp⟩⟩
end Eden
