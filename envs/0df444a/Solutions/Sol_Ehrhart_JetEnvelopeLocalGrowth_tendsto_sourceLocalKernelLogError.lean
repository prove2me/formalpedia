-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.tendsto_sourceLocalKernelLogError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/fcff5406-3897-43c1-9e86-f68204623214

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
namespace Ehrhart.JetEnvelopeLocalGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n) :
    Tendsto (sourceLocalKernelLogError K) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun k : ℕ => Real.log (sourceLocalPolynomialConstant K) /
        (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 one_ne_zero).comp hnat
    exact h.congr' (Filter.Eventually.of_forall fun _ => by simp)
  have hsum := hconst.add (hlog.const_mul (3 * (n : ℝ)))
  have heq : sourceLocalKernelLogError K =
      (fun k : ℕ =>
        Real.log (sourceLocalPolynomialConstant K) / (k : ℝ) +
          3 * (n : ℝ) * (Real.log (k : ℝ) / (k : ℝ))) := by
    funext k
    unfold sourceLocalKernelLogError
    rw [add_div]
    ring
  rw [heq]
  simpa using hsum
end Ehrhart.JetEnvelopeLocalGrowth
