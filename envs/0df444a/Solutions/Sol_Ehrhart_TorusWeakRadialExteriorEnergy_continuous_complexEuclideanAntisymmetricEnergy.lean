-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorEnergy.continuous_complexEuclideanAntisymmetricEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/7837c1cf-4ded-4bb5-ba67-6b2e9ce43c5e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakRadialExteriorEnergy
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology
namespace Ehrhart.TorusWeakRadialExteriorEnergy
theorem _root_.solution
    {n : ℕ} :
    Continuous (complexEuclideanAntisymmetricEnergy (n := n)) := by
  unfold complexEuclideanAntisymmetricEnergy
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hij : Continuous
      (fun M : EuclideanSpace ℂ (Fin n × Fin n) =>
        M (i, j) - M (j, i)) :=
    (PiLp.continuous_apply 2
      (fun _ : Fin n × Fin n => ℂ) (i, j)).sub
      (PiLp.continuous_apply 2
        (fun _ : Fin n × Fin n => ℂ) (j, i))
  exact hij.mul (Complex.continuous_conj.comp hij)
end Ehrhart.TorusWeakRadialExteriorEnergy
