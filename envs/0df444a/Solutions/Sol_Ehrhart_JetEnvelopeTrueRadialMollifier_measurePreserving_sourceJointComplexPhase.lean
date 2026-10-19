-- Prove2me | solution 1 for Ehrhart.JetEnvelopeTrueRadialMollifier.measurePreserving_sourceJointComplexPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/a2c8897e-358e-4247-8eac-04e8c50df9d5

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
    MeasurePreserving (fun q : SourceJointComplexCover n => u • q)
      (volume : Measure (SourceJointComplexCover n))
      (volume : Measure (SourceJointComplexCover n)) := by
  have hc : MeasurePreserving (fun z : ℂ => u * z)
      (volume : Measure ℂ) (volume : Measure ℂ) := by
    let a : Circle :=
      ⟨u, by simpa [Submonoid.unitSphere] using hu⟩
    have hrotation : MeasurePreserving (rotation a)
        (volume : Measure ℂ) (volume : Measure ℂ) :=
      (rotation a).measurePreserving
    change MeasurePreserving (rotation a)
      (volume : Measure ℂ) (volume : Measure ℂ)
    exact hrotation
  have hp : MeasurePreserving
      (fun z : Fin n → ℂ => fun i => u * z i)
      (volume : Measure (Fin n → ℂ))
      (volume : Measure (Fin n → ℂ)) := by
    exact MeasureTheory.measurePreserving_pi
      (fun _ : Fin n => (volume : Measure ℂ))
      (fun _ : Fin n => (volume : Measure ℂ))
      (fun _ => hc)
  exact hp.prod hc
end Ehrhart.JetEnvelopeTrueRadialMollifier
