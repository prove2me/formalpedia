-- Prove2me | solution 1 for Ehrhart.JetEnvelopeLocalGrowth.sourceLocalBoxRadius_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/3839ce1c-1006-4e05-b4c6-5d6eca77dc4b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_sourceLocalBoxScale_pos

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
theorem _root_.solution {R t : ℝ}
    (hR : 0 < R) (ht : 0 ≤ t) :
    sourceLocalBoxRadius R t ≤ 1 := by
  unfold sourceLocalBoxRadius
  calc
    sourceLocalBoxScale R * Real.exp (-t / 2) ≤
      sourceLocalBoxScale R * 1 := by
        gcongr
        · exact (sourceLocalBoxScale_pos hR).le
        · exact Real.exp_le_one_iff.mpr (by linarith)
    _ ≤ 1 := by
      simp [sourceLocalBoxScale]
end Ehrhart.JetEnvelopeLocalGrowth
