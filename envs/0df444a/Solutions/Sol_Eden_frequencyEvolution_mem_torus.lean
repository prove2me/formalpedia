-- Prove2me | solution 1 for Eden.frequencyEvolution_mem_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:47.524923+00:00
-- url     : https://prove2.me/submissions/169f7f97-eafa-42b3-bd14-0d9bab514bd2

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_FrequencyAttractor
import Theorems.Thm_Eden_frequencyCorrection_mem_torus_iff
import Theorems.Thm_Eden_frequencyEvolution_eq_correction
import Theorems.Thm_Eden_torus_invariant_all_real


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c ν t : ℝ) {p : PhaseSpace} (hp : p ∈ torus) :
    frequencyEvolution c ν t p ∈ torus := by
  rw [frequencyEvolution_eq_correction, frequencyCorrection_mem_torus_iff]
  exact torus_invariant_all_real c t hp
end Eden
