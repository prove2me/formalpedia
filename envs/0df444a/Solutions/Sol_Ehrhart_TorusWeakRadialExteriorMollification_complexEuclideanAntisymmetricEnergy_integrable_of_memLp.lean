-- Prove2me | solution 1 for Ehrhart.TorusWeakRadialExteriorMollification.complexEuclideanAntisymmetricEnergy_integrable_of_memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/b500749c-1318-4947-9900-1b4d65cdd223

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_complexEuclidean_antisymmetric_energy_le_two_norm_sq
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorEnergy_norm_complexEuclideanAntisymmetricEnergy
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorEnergy_continuous_complexEuclideanAntisymmetricEnergy

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
    Integrable
      (fun x : X => complexEuclideanAntisymmetricEnergy (M x)) μ := by
  have hsq : Integrable (fun x : X => ‖M x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hM.aestronglyMeasurable).mp hM
  apply (hsq.const_mul (2 : ℝ)).mono'
    ((continuous_complexEuclideanAntisymmetricEnergy (n := n)).comp_aestronglyMeasurable
      hM.aestronglyMeasurable)
  filter_upwards [] with x
  rw [norm_complexEuclideanAntisymmetricEnergy]
  exact complexEuclidean_antisymmetric_energy_le_two_norm_sq (M x)
end Ehrhart.TorusWeakRadialExteriorMollification
