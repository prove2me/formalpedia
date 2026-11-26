-- Prove2me | solution 1 for Eden.tendsto_spectrumInterpolation_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:31.703803+00:00
-- url     : https://prove2.me/submissions/c8118b56-61d1-4a54-8251-98489141efcf

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
import Theorems.Thm_Eden_tendstoUniformly_spectrumInterpolation
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) (d : ℝ) :
    Tendsto (fun t => spectrumInterpolation (normalizedLogSingularValues c t p) d)
      atTop (𝓝 (spectrumInterpolation (lyapunovExponent c p) d)) := by
  exact (tendstoUniformly_spectrumInterpolation
    (tendsto_pi_nhds.mpr (fun i => tendsto_lyapunovExponent c p i))).tendsto_at d
end Eden
