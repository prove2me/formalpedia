-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/e4841ac9-f78e-4c18-a4cd-f19e5d463c0b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_finiteEnergySourceLegendre_interior
import Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_tendsto_unitPartition_tag_index
import Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_tendsto_momentTaggedLaurentObservable_unitPartition_tag

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      Tendsto
        (fun k : ℕ =>
          (interior K.carrier).indicator
            (momentTaggedLaurentObservable F (k + 1) f)
            (BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop
        (𝓝 ((interior K.carrier).indicator
          (fun u : Space n =>
            f (SpatialBergmanFatouScheffe.actualGradient
              (legendreTransform F.potential) u)) x)) := by
  have hfront :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        x ∉ frontier (interior K.carrier) :=
    compl_mem_ae_iff.mpr
      (K.convex.interior.addHaar_frontier
        (volume : Measure (Space n)))
  filter_upwards [hfront,
    ae_differentiableAt_finiteEnergySourceLegendre_interior
      F htransport] with x hxfront hxdual
  by_cases hx : x ∈ interior K.carrier
  · have htags :
        ∀ᶠ k : ℕ in atTop,
          BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x) ∈
            interior K.carrier :=
      (tendsto_unitPartition_tag_index x).eventually
        (isOpen_interior.mem_nhds hx)
    rw [Set.indicator_of_mem hx]
    apply
      (tendsto_momentTaggedLaurentObservable_unitPartition_tag
        F htransport hx (hxdual hx) f hf C hC).congr'
    filter_upwards [htags] with k hk
    simp [Set.indicator_of_mem hk]
  · have hxclosure : x ∉ closure (interior K.carrier) := by
      intro hcl
      apply hxfront
      change x ∈ closure (interior K.carrier) \
        interior (interior K.carrier)
      exact ⟨hcl, by simpa using hx⟩
    have hcomp :
        (closure (interior K.carrier))ᶜ ∈ 𝓝 x :=
      isClosed_closure.isOpen_compl.mem_nhds hxclosure
    have htags :
        ∀ᶠ k : ℕ in atTop,
          BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x) ∉
            interior K.carrier := by
      have hout :=
        (tendsto_unitPartition_tag_index x).eventually hcomp
      filter_upwards [hout] with k hk
      exact fun hmem => hk (subset_closure hmem)
    rw [Set.indicator_of_notMem hx]
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [htags] with k hk
    simp [Set.indicator_of_notMem hk]
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
