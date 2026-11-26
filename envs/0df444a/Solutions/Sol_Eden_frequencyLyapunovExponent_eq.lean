-- Prove2me | solution 1 for Eden.frequencyLyapunovExponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:54.048076+00:00
-- url     : https://prove2.me/submissions/ca3c41bf-bf37-4be5-be89-c34cf6f0b0d7

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_tendsto_frequencyLogSingularValue

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    frequencyLyapunovExponent c ν p i = lyapunovExponent c p i :=
  (tendsto_frequencyLogSingularValue c ν p i).limUnder_eq
end Eden
