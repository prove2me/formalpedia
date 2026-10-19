-- Prove2me | solution 1 for Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz.dense_finiteEnergySourceInteriorDifferentiability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/116c716b-aa29-408b-a839-97ff314bb122

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_ae_finiteEnergySourceGradient_mem_interior_volume

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
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Dense
      {x : Space n |
        DifferentiableAt ℝ
            (F.potential : Space n → ℝ) x ∧
          SpatialBergmanFatouScheffe.actualGradient
            F.potential x ∈ interior K.carrier} := by
  apply MeasureTheory.Measure.dense_of_ae
    (μ := (volume : Measure (Space n)))
  exact (ae_differentiableAt_finiteEnergySource F).and
    (ae_finiteEnergySourceGradient_mem_interior_volume F htransport)
end Ehrhart.BergmanJetGlobalLogKernelEquiLipschitz
