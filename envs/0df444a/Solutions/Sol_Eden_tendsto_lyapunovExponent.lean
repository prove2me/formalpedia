-- Prove2me | solution 1 for Eden.tendsto_lyapunovExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:43.595169+00:00
-- url     : https://prove2.me/submissions/73c20ec0-b727-42d3-8886-198f0c5fe630

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_tendsto_normalizedLogSingularValues
import Theorems.Thm_Eden_lyapunovExponent_eq_descending

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) := by
  rw [lyapunovExponent_eq_descending]
  exact tendsto_pi_nhds.mp (tendsto_normalizedLogSingularValues c p) i
end Eden
