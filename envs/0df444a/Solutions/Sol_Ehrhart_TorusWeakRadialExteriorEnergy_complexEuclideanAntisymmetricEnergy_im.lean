-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorEnergy.complexEuclideanAntisymmetricEnergy_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/c6d5f949-d900-4858-8d5e-dfde0b31cec1

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
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    (complexEuclideanAntisymmetricEnergy M).im = 0 := by
  unfold complexEuclideanAntisymmetricEnergy
  change
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) /
      ((2 : ℝ) : ℂ)).im = 0
  rw [Complex.div_ofReal_im]
  simp_rw [Complex.im_sum, Complex.mul_conj, Complex.ofReal_im]
  simp
end Ehrhart.TorusWeakRadialExteriorEnergy
