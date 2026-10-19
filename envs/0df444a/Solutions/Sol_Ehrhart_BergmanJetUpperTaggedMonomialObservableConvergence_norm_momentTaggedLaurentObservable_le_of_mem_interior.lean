-- Prove2me | solution 1 for Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.norm_momentTaggedLaurentObservable_le_of_mem_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/010f885c-2d70-4884-8f78-043b1653fed4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDiagonalObservableLatticeIdentity_abs_momentNormalizedLaurentObservable_le

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
    ∀ k : ℕ, ∀ u ∈ interior K.carrier,
      ‖momentTaggedLaurentObservable F k f u‖ ≤ C := by
  classical
  have hCnonneg : 0 ≤ C :=
    (abs_nonneg (f (0 : Space n))).trans (hC 0)
  intro k u hu
  unfold momentTaggedLaurentObservable
  split_ifs with hk hl
  · let v : monomialIndex K k := ⟨u, ⟨hu, hl⟩⟩
    simpa [v, Real.norm_eq_abs] using
      abs_momentNormalizedLaurentObservable_le
        K hk F htransport f hf C hC v
  · simpa using hCnonneg
  · simpa using hCnonneg
end Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
