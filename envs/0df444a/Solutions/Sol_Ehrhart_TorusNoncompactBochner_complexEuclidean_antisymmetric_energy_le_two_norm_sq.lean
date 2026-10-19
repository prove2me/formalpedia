-- Prove2me | solution 1 for Ehrhart.TorusNoncompactBochner.complexEuclidean_antisymmetric_energy_le_two_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/50e1df48-802f-43ff-a47a-79d5168b38ca

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_complex_norm_sub_sq_le_two_mul_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusNoncompactBochner
theorem _root_.solution
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) / 2 : ℂ).re
      ≤ 2 * ‖M‖ ^ 2 := by
  change
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) / ((2 : ℝ) : ℂ)).re
      ≤ 2 * ‖M‖ ^ 2
  rw [Complex.div_ofReal_re]
  simp_rw [Complex.re_sum, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hsum :
      ∑ i : Fin n, ∑ j : Fin n, ‖M (i, j) - M (j, i)‖ ^ 2 ≤
        ∑ i : Fin n, ∑ j : Fin n,
          2 * (‖M (i, j)‖ ^ 2 + ‖M (j, i)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ =>
        complex_norm_sub_sq_le_two_mul_add (M (i, j)) (M (j, i))))
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, ‖M (j, i)‖ ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, ‖M (i, j)‖ ^ 2 := by
    rw [Finset.sum_comm]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  nlinarith
end Ehrhart.TorusNoncompactBochner
