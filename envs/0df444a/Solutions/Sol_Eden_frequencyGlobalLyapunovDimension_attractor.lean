-- Prove2me | solution 1 for Eden.frequencyGlobalLyapunovDimension_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:56.347731+00:00
-- url     : https://prove2.me/submissions/085bb2a6-f2b0-4049-89a1-6c48871de54a

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_frequencyGlobalLyapunovDimension_eq
import Theorems.Thm_Eden_globalLyapunovDimension_attractor


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) (ν : ℝ) :
    frequencyGlobalLyapunovDimension c ν attractor = 4 + 4 / c := by
  rw [frequencyGlobalLyapunovDimension_eq, globalLyapunovDimension_attractor hc]
end Eden
