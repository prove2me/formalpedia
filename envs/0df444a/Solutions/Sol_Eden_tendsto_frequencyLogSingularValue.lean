-- Prove2me | solution 1 for Eden.tendsto_frequencyLogSingularValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:42.166069+00:00
-- url     : https://prove2.me/submissions/f1119988-8447-4d01-9d24-d6ed747cfd2f

import Definitions.Def_Eden_FrequencySingularValues
import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_FrequencyDimensions
import Theorems.Thm_Eden_singularValues_frequencyEvolution_eq
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c ν : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (frequencyEvolution c ν t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i)) := by
  apply (tendsto_lyapunovExponent c p i).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [singularValues_frequencyEvolution_eq c ν ht p]
end Eden
