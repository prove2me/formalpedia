-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorEnergy.complexEuclideanAntisymmetricEnergy_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/9f65b9ec-a2f0-4bba-b09c-980c123c4a6b

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
    0 ≤ (complexEuclideanAntisymmetricEnergy M).re := by
  unfold complexEuclideanAntisymmetricEnergy
  change
    0 ≤ ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) /
      ((2 : ℝ) : ℂ)).re
  rw [Complex.div_ofReal_re]
  simp_rw [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  positivity
end Ehrhart.TorusWeakRadialExteriorEnergy
