-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifierAdjoint.complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/d74e6080-110a-4073-9fb1-45069dbc7233

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_complexCoverWeight
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_holomorphicCoordinate_mul
import Theorems.Thm_Ehrhart_TorusDensityAdaptedWeightedAdjoint_holomorphicCoordinate_complexCoverWeight
import Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_contDiff_translatedDensityCancelledCoverKernel
import Theorems.Thm_Ehrhart_TorusClosedMollifierAdjoint_complexCoverWeight_mul_translatedDensityCancelledCoverKernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusClosedMollifierAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusClosedMollifierAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 1 (angularCoverPotential a))
    (k : ℕ) (x y : LogSpace n) (j : Fin n) :
    complexCoverWeight (angularCoverPotential a) y *
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          (translatedDensityCancelledCoverKernel a k x z : ℂ)) y j) =
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) : ℂ) *
        holomorphicCoordinate
          (fun z : LogSpace n =>
            (angularCoverPotential a z : ℂ)) y j := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let χ : LogSpace n → ℝ :=
    translatedDensityCancelledCoverKernel a k x
  let d : LogSpace n → ℂ :=
    complexCoverWeight (angularCoverPotential a)
  let ψ : LogSpace n → ℂ := fun z => (χ z : ℂ)
  let η : LogSpace n → ℂ := fun z => (κ (x - z) : ℂ)
  have hχ : ContDiff ℝ 1 χ :=
    contDiff_translatedDensityCancelledCoverKernel ha k x
  have hψ : ContDiff ℝ 1 ψ :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hd : ContDiff ℝ 1 d := contDiff_complexCoverWeight ha
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hηreal : Differentiable ℝ (fun z : LogSpace n => κ (x - z)) :=
    (hκ.comp (contDiff_const.sub contDiff_id)).differentiable (by simp)
  have hproduct : (fun z : LogSpace n => d z * ψ z) = η := by
    funext z
    exact complexCoverWeight_mul_translatedDensityCancelledCoverKernel
      a k x z
  have hmul :
      holomorphicCoordinate η y j =
        d y * holomorphicCoordinate ψ y j +
          ψ y *
            (-d y * holomorphicCoordinate
              (fun z : LogSpace n =>
                (angularCoverPotential a z : ℂ)) y j) := by
    calc
      holomorphicCoordinate η y j =
          holomorphicCoordinate (fun z => d z * ψ z) y j := by
            rw [hproduct]
      _ = d y * holomorphicCoordinate ψ y j +
          ψ y * holomorphicCoordinate d y j :=
        holomorphicCoordinate_mul
          (hd.differentiable (by simp))
          (hψ.differentiable (by simp)) y j
      _ = _ := by
        rw [holomorphicCoordinate_complexCoverWeight ha y j]
  change
    d y * conj (barPartialCoordinate ψ y j) =
      conj (barPartialCoordinate η y j) +
      η y * holomorphicCoordinate
        (fun z : LogSpace n =>
          (angularCoverPotential a z : ℂ)) y j
  rw [conj_barPartialCoordinate_real
        (hχ.differentiable (by simp)) y j,
      conj_barPartialCoordinate_real hηreal y j]
  have hp := congrFun hproduct y
  rw [← hp]
  rw [hmul]
  ring
end Ehrhart.TorusClosedMollifierAdjoint
