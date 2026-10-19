-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularMollifiedPhysicalAdjointDriftCommutator_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/05fa6543-e49a-442a-8437-c682a6b98ce0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedAdjointMollification_finite_complex_local_square_integral_sum_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularFormCoordinateCoverLift_holomorphicDriftCommutator_tendsto_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousFriedrichs
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusDolbeault
open TorusWeightedBaseAE TorusWeakDolbeaultMollification TorusStrongCoverMollificationDensity
open TorusStrongWeightedTorusDescent TorusFriedrichsMollifierEstimates
open TorusWeightedAdjointMollification BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousFriedrichs
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖angularMollifiedPhysicalAdjointDriftCommutator W k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply finite_complex_local_square_integral_sum_tendsto_zero
    Finset.univ _ hK
  · intro j _ k
    apply continuous_normalizedCoverComplexDriftCommutator
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j)
    exact (contDiff_holomorphicCoordinate
      (Complex.ofRealCLM.contDiff.comp ha2) j).continuous
  · intro j _
    exact
      angularFormCoordinateCoverLift_holomorphicDriftCommutator_tendsto_zero
        ha ha2 W j j hK
end Ehrhart.TorusHomogeneousFriedrichs
