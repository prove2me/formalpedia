-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorMollification.integral_complexEuclideanAntisymmetricEnergy_le_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/2da32d29-6bb7-475e-9ae4-b412a08d81be

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_complexEuclidean_antisymmetric_energy_le_two_norm_sq
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorMollification_complexEuclideanAntisymmetricEnergy_integrable_of_memLp

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakRadialExteriorMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedPoincare WeightedBrascampLieb
open WeightedResolventConstantCore EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open TorusMollifiedBochner TorusNoncompactBochner TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusWeakRadialExteriorMollification
theorem _root_.solution
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {M : X → EuclideanSpace ℂ (Fin n × Fin n)}
    (hM : MemLp M 2 μ) :
    (∫ x : X,
      complexEuclideanAntisymmetricEnergy (M x) ∂μ).re ≤
      2 * ‖hM.toLp M‖ ^ 2 := by
  have hsq : Integrable (fun x : X => ‖M x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hM.aestronglyMeasurable).mp hM
  have hext := complexEuclideanAntisymmetricEnergy_integrable_of_memLp hM
  calc
    (∫ x : X,
      complexEuclideanAntisymmetricEnergy (M x) ∂μ).re =
        ∫ x : X,
          (complexEuclideanAntisymmetricEnergy (M x)).re ∂μ :=
            (integral_re hext).symm
    _ ≤ ∫ x : X, (2 : ℝ) * ‖M x‖ ^ 2 ∂μ :=
      integral_mono hext.re (hsq.const_mul 2)
        (fun x => complexEuclidean_antisymmetric_energy_le_two_norm_sq
          (M x))
    _ = 2 * ∫ x : X, ‖M x‖ ^ 2 ∂μ :=
      integral_const_mul 2 _
    _ = 2 * ‖hM.toLp M‖ ^ 2 := by
      congr 1
      rw [complexLp_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [hM.coeFn_toLp] with x hx
      rw [hx]
end Ehrhart.TorusWeakRadialExteriorMollification
