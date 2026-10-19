-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalSchwarzRatio_sq_mul_exp_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/1c2468ae-8980-4848-b7b1-70655031631a

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
    {d R t : ℝ} (hd : 0 ≤ d) (hR : 0 < R)
    (hshrinking : d < R * Real.exp (-t / 2)) :
    (d / R) ^ 2 * Real.exp t ≤ 1 := by
  have hratio : d / R < Real.exp (-t / 2) := by
    apply (div_lt_iff₀ hR).mpr
    simpa [mul_comm] using hshrinking
  have hq : 0 ≤ d / R := div_nonneg hd hR.le
  have hsq : (d / R) ^ 2 ≤ Real.exp (-t) := by
    calc
      (d / R) ^ 2 ≤ Real.exp (-t / 2) ^ 2 :=
        (sq_le_sq₀ hq (Real.exp_pos _).le).mpr hratio.le
      _ = Real.exp (-t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (d / R) ^ 2 * Real.exp t ≤
        Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add]
      simp
end Ehrhart.JetEnvelopeLocalGrowth
