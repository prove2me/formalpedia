-- Prove2me | solution 1 for Eden.continuous_spectrumInterpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:12.904018+00:00
-- url     : https://prove2.me/submissions/a2515545-5d7b-4497-851c-0ef3f06ed70f

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
import Theorems.Thm_Eden_continuous_singularWeight


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (a : Fin 5 → ℝ) :
    Continuous (spectrumInterpolation a) := by
  unfold spectrumInterpolation
  exact continuous_finsetSum _ (fun i _ => (continuous_singularWeight i).mul continuous_const)
end Eden
