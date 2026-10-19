-- Prove2me | solution 1 for Ehrhart.WeightedTorusDolbeault.smoothAngularDolbeaultGraph_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/8fb46af2-9518-46a4-b20b-d842432a1623

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusDolbeault
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hcont : ContDiff ℝ 3 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    WithLp.toLp 2
      (angularScalarL2OfRepresentative a F hF,
       angularBarPartialL2OfRepresentative a F hD) ∈
        angularDolbeaultGraph a := by
  apply (Submodule.span ℂ
    (smoothAngularDolbeaultGraphSet a)).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨F, hcont, hperiod, hcompact, hF, hD, rfl⟩
end Ehrhart.WeightedTorusDolbeault
