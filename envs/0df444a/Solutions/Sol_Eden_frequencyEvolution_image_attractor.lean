-- Prove2me | solution 1 for Eden.frequencyEvolution_image_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:50.524606+00:00
-- url     : https://prove2.me/submissions/896ac8dd-ed99-496c-b8f6-796e1cc62e97

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_FrequencyAttractor
import Theorems.Thm_Eden_evolution_image_attractor
import Theorems.Thm_Eden_frequencyCorrection_image_attractor
import Theorems.Thm_Eden_frequencyEvolution_eq_correction


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    frequencyEvolution c ν t '' attractor = attractor := by
  have he : frequencyEvolution c ν t = (frequencyCorrection ν t) ∘ evolution c t :=
    funext (frequencyEvolution_eq_correction c ν t)
  rw [he, Set.image_comp, evolution_image_attractor c ht, frequencyCorrection_image_attractor]
end Eden
