-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.finiteEnergySourceNormalized_actualGradient_phase_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/bfd99736-8d8d-4189-a5f9-ba99383a1668

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (z : Space n) :
    phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) z ≤
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) x := by
  have h := finiteEnergySourcePhase_actualGradient_le F x hx z
  unfold phase at h ⊢
  simp only [momentNormalizedPotential]
  linarith
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
