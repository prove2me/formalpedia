-- Prove2me | solution 1 for Eden.attractor_frequencyUniformlyAttractsBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:25.025989+00:00
-- url     : https://prove2.me/submissions/0fd7f0c5-9192-491b-b0bc-27af57c21aba

import Definitions.Def_Eden_FrequencyRotation
import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_FrequencyAttractor
import Theorems.Thm_Eden_attractor_uniformlyAttractsBounded
import Theorems.Thm_Eden_frequencyCorrection_mem_attractor_iff
import Theorems.Thm_Eden_frequencyEvolution_eq_correction


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) (ν : ℝ) :
    FrequencyUniformlyAttractsBounded c ν attractor := by
  intro B hB ε hε
  obtain ⟨T, hT₀, hT⟩ := attractor_uniformlyAttractsBounded hc B hB ε hε
  refine ⟨T, hT₀, ?_⟩
  intro t ht p hp
  obtain ⟨q, hq, hd⟩ := hT t ht p hp
  refine ⟨frequencyCorrection ν t q, (frequencyCorrection_mem_attractor_iff ν t q).2 hq, ?_⟩
  rw [frequencyEvolution_eq_correction, (frequencyCorrection ν t).dist_map]
  exact hd
end Eden
