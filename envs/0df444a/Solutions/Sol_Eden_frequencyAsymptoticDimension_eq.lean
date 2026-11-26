-- Prove2me | solution 1 for Eden.frequencyAsymptoticDimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:53.263606+00:00
-- url     : https://prove2.me/submissions/ec95c8a6-7b23-40eb-a1e0-564efc4c4704

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_frequencyLyapunovExponent_eq

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) :
    frequencyAsymptoticDimension c ν p = asymptoticDimension c p := by
  unfold frequencyAsymptoticDimension asymptoticDimension
  congr 1
  funext i
  exact frequencyLyapunovExponent_eq c ν p i
end Eden
