-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorEnergy.norm_complexEuclideanAntisymmetricEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/bf6b9874-390d-4617-a127-870833709d24

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorEnergy_complexEuclideanAntisymmetricEnergy_im
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorEnergy_complexEuclideanAntisymmetricEnergy_re_nonneg

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
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖complexEuclideanAntisymmetricEnergy M‖ =
      (complexEuclideanAntisymmetricEnergy M).re := by
  have hre : complexEuclideanAntisymmetricEnergy M =
      (((complexEuclideanAntisymmetricEnergy M).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [complexEuclideanAntisymmetricEnergy_im M]
  calc
    ‖complexEuclideanAntisymmetricEnergy M‖ =
      ‖(((complexEuclideanAntisymmetricEnergy M).re : ℝ) : ℂ)‖ :=
        congrArg norm hre
    _ = |(complexEuclideanAntisymmetricEnergy M).re| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (complexEuclideanAntisymmetricEnergy M).re :=
      abs_of_nonneg (complexEuclideanAntisymmetricEnergy_re_nonneg M)
end Ehrhart.TorusWeakRadialExteriorEnergy
