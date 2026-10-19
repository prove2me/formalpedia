-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousFriedrichs.angularFormCoordinateCoverLift_holomorphicDriftCommutator_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/b4f079cc-cf19-41bd-857d-13925ad1a36b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousFriedrichs_angularFormCoordinateCoverLift_complexDriftCommutator_tendsto_zero

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
    (W : angularWeightedFormL2 a) (i j : Fin n)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator
            (fun z => holomorphicCoordinate
              (fun w => (angularCoverPotential a w : ℂ)) z i)
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  apply angularFormCoordinateCoverLift_complexDriftCommutator_tendsto_zero
    ha W j (K := K) (hK := hK)
  exact (contDiff_holomorphicCoordinate
    (Complex.ofRealCLM.contDiff.comp ha2) i).continuous
end Ehrhart.TorusHomogeneousFriedrichs
