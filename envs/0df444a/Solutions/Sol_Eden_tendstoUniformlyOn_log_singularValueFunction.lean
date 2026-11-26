-- Prove2me | solution 1 for Eden.tendstoUniformlyOn_log_singularValueFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:35.448537+00:00
-- url     : https://prove2.me/submissions/52768d91-3814-466e-9b26-8cac3474acd5

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SingularValueFunction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_Eden_LogarithmicInterpolation
import Theorems.Thm_Eden_log_singularValueFunction_div_time
import Theorems.Thm_Eden_tendstoUniformly_spectrumInterpolation
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) := by
  have hvec : Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (lyapunovExponent c p)) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_lyapunovExponent c p i)
  have h := Metric.tendstoUniformly_iff.mp (tendstoUniformly_spectrumInterpolation hvec)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop (0 : ℝ)] with t hbound ht d hd
  rw [log_singularValueFunction_div_time c ht p d]
  exact hbound d
end Eden
