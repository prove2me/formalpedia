-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/229a959d-623c-4676-8b38-ac10d6349667

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ} {g h : LogSpace n → ℂ}
    (hgh : g =ᵐ[(volume : Measure (LogSpace n))] h)
    (k : ℕ) :
    normalizedCoverMollification g k =
      normalizedCoverMollification h k := by
  unfold normalizedCoverMollification
  exact MeasureTheory.convolution_congr
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (Filter.Eventually.of_forall (fun _ => rfl)) hgh
end Ehrhart.TorusStrongCoverMollificationDensity
