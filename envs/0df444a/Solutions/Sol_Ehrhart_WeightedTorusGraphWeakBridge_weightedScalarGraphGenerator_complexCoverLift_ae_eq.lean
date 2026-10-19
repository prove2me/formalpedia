-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.weightedScalarGraphGenerator_complexCoverLift_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/053faf63-4a1c-40a7-a8ef-045dff6917db

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedTorus_complexCoverLift_ae_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        torusScalarL2OfRepresentative φ F hF z) =ᵐ[
          (volume : Measure (TorusCharacters.LogSpace n))] F := by
  have h := weightedTorus_complexCoverLift_ae_eq hφ hF.coeFn_toLp
  change
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        torusScalarL2OfRepresentative φ F hF z) =ᵐ[
          (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift (torusScalarRepresentative F)
    at h
  simpa [complexTorusCoverLift_torusScalarRepresentative_eq F hperiod]
    using h
end Ehrhart.WeightedTorusGraphWeakBridge
