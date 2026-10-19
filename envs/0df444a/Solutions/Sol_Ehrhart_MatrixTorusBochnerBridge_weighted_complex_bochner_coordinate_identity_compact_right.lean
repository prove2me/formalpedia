-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.weighted_complex_bochner_coordinate_identity_compact_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/5adb07e5-76a6-46a1-b4c7-f61be62736ef

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_conj
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_barPartial_hermitian_integration_by_parts
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_barPartialCoordinate
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_weightedHolomorphicDerivative
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_barPartialCoordinate
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_weightedHolomorphicDerivative_commutator
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_of_continuous_compact_cover
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_weighted_holomorphic_hermitian_integration_by_parts_compact_right

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hGcompact : HasCompactSupport G)
    (i j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative a F i z *
        conj (weightedHolomorphicDerivative a G j z)
      ∂(coverWeightedMeasure a)) =
    ∫ z : TorusCharacters.LogSpace n,
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) +
       (F z * complexHessian a z i j) * conj (G z))
      ∂(coverWeightedMeasure a) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  have haone : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hfone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hgone : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hFbar : ContDiff ℝ 1
      (fun z : E => barPartialCoordinate F z j) :=
    contDiff_barPartialCoordinate hF j
  have hGc : HasCompactSupport (fun z : E => conj (G z)) :=
    compactSupport_conj hGcompact
  have hfirst := weighted_barPartial_hermitian_integration_by_parts
    haone (contDiff_weightedHolomorphicDerivative ha hF i)
    hgone hGcompact j
  have hfirstrev :
      (∫ z : E,
        weightedHolomorphicDerivative a F i z *
          conj (weightedHolomorphicDerivative a G j z) ∂μ) =
      -(∫ z : E,
        barPartialCoordinate
          (fun w => weightedHolomorphicDerivative a F i w) z j *
            conj (G z) ∂μ) := by
    linear_combination hfirst
  have hsecond :=
    weighted_holomorphic_hermitian_integration_by_parts_compact_right
      haone hFbar hgone hGcompact i
  have hcore : Integrable
      (fun z : E =>
        weightedHolomorphicDerivative a
          (fun w => barPartialCoordinate F w j) i z * conj (G z)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedHolomorphicDerivative haone hFbar i).mul
        (Complex.continuous_conj.comp hG.continuous))
    exact hGc.mul_left
  have hcurv : Integrable
      (fun z : E =>
        (F z * complexHessian a z i j) * conj (G z)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((hF.continuous.mul
        (continuous_complexHessian ha i j)).mul
          (Complex.continuous_conj.comp hG.continuous))
    exact hGc.mul_left
  have hcross : Integrable
      (fun z : E =>
        barPartialCoordinate F z j *
          conj (barPartialCoordinate G z i)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_barPartialCoordinate hfone j).mul
        (Complex.continuous_conj.comp
          (continuous_barPartialCoordinate hgone i)))
    exact (compactSupport_conj
      (compactSupport_barPartialCoordinate hGcompact i)).mul_left
  change
    (∫ z : E,
      weightedHolomorphicDerivative a F i z *
        conj (weightedHolomorphicDerivative a G j z) ∂μ) =
    ∫ z : E,
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) +
       (F z * complexHessian a z i j) * conj (G z)) ∂μ
  calc
    _ = -(∫ z : E,
      barPartialCoordinate
        (fun w => weightedHolomorphicDerivative a F i w) z j *
          conj (G z) ∂μ) := hfirstrev
    _ = -(∫ z : E,
      (weightedHolomorphicDerivative a
          (fun w => barPartialCoordinate F w j) i z * conj (G z) -
        (F z * complexHessian a z i j) * conj (G z)) ∂μ) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [] with z
      rw [barPartial_weightedHolomorphicDerivative_commutator
        ha hF z i j]
      ring
    _ = -((∫ z : E,
      weightedHolomorphicDerivative a
        (fun w => barPartialCoordinate F w j) i z * conj (G z) ∂μ) -
      (∫ z : E,
        (F z * complexHessian a z i j) * conj (G z) ∂μ)) := by
      rw [MeasureTheory.integral_sub hcore hcurv]
    _ = (∫ z : E,
      barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) ∂μ) +
      (∫ z : E,
        (F z * complexHessian a z i j) * conj (G z) ∂μ) := by
      rw [hsecond]
      ring
    _ = _ := (MeasureTheory.integral_add hcross hcurv).symm
end Ehrhart.MatrixTorusBochnerBridge
