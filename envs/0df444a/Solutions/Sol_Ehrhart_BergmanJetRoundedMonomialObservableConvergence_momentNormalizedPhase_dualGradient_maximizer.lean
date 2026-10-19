-- Prove2me | solution 1 for Ehrhart.BergmanJetRoundedMonomialObservableConvergence.momentNormalizedPhase_dualGradient_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/da81d239-e5c3-4469-9560-7b28d7ec94ea

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetPhaseLaplace_exists_momentNormalizedPhaseMaximizer
import Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
import Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_momentNormalized_phaseMaximizer_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetRoundedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open BergmanJetPhaseLaplace BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology
namespace Ehrhart.BergmanJetRoundedMonomialObservableConvergence
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u) :
    ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F)
          (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u) := by
  obtain ⟨x₀, hx₀⟩ :=
    exists_momentNormalizedPhaseMaximizer F htransport hu
  have hgradient :
      SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u = x₀ :=
    finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
      F htransport hu hdu x₀
        ((momentNormalized_phaseMaximizer_iff F u x₀).mp hx₀)
  simpa [hgradient] using hx₀
end Ehrhart.BergmanJetRoundedMonomialObservableConvergence
