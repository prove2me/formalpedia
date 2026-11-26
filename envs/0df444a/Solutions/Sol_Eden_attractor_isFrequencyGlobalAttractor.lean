-- Prove2me | solution 1 for Eden.attractor_isFrequencyGlobalAttractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:17:50.73935+00:00
-- url     : https://prove2.me/submissions/b2c8ba60-c87d-458b-b950-8aaeed0f6013

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_FrequencyAttractor
import Theorems.Thm_Eden_frequencyEvolution_image_attractor
import Theorems.Thm_Eden_attractor_frequencyUniformlyAttractsBounded
import Theorems.Thm_Eden_attractor_nonempty
import Theorems.Thm_Eden_isCompact_attractor


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) (ν : ℝ) :
    IsFrequencyGlobalAttractor c ν attractor :=
  ⟨attractor_nonempty, isCompact_attractor, fun _ ht => frequencyEvolution_image_attractor c ν ht,
    attractor_frequencyUniformlyAttractsBounded hc ν⟩
end Eden
