-- Prove2me | solution 1 for Eden.tendsto_frequencyLyapunovExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:00.190234+00:00
-- url     : https://prove2.me/submissions/564d5595-9ee4-4396-be60-4d4796a1325b

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_tendsto_frequencyLogSingularValue
import Theorems.Thm_Eden_frequencyLyapunovExponent_eq

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (frequencyLyapunovExponent c ν p i)) := by
  rw [frequencyLyapunovExponent_eq]
  exact tendsto_frequencyLogSingularValue c ν p i
end Eden
