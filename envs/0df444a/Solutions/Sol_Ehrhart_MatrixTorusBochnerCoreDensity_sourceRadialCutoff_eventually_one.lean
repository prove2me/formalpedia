-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerCoreDensity.sourceRadialCutoff_eventually_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/d487174f-3560-4461-ac8f-a5fc1cb4f865

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedResolventConstantCore_growingBump_eventually_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerCoreDensity
open Set Function MeasureTheory Filter Matrix
open MatrixTorusBochnerCore WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerCoreDensity
theorem _root_.solution
    {n : ℕ}
    (p : WeightedTorusHilbert.LogTorus n) :
    ∀ᶠ m : ℕ in atTop, sourceRadialCutoff m p = 1 :=
  growingBump_eventually_one p.1
end Ehrhart.MatrixTorusBochnerCoreDensity
