-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.measurableEmbedding_sourceJointComplexPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/3f7e3054-8ed4-4808-a1ae-d08888282ed8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
attribute [local instance] Ehrhart.JetEnvelopeTrueRadialMollifier.sourceJointCoverVolume_isAddHaar
namespace Ehrhart.JetEnvelopeTrueRadialMollifier
theorem _root_.solution {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurableEmbedding
      (fun q : SourceJointComplexCover n => u • q) := by
  let a : Circle :=
    ⟨u, by simpa [Submonoid.unitSphere] using hu⟩
  let e : ℂ ≃ᵐ ℂ :=
    (rotation a).toHomeomorph.toMeasurableEquiv
  let ep : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    MeasurableEquiv.piCongrRight (fun _ : Fin n => e)
  let ej : SourceJointComplexCover n ≃ᵐ
      SourceJointComplexCover n := ep.prodCongr e
  exact ej.measurableEmbedding
end Ehrhart.JetEnvelopeTrueRadialMollifier
