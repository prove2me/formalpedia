-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauSlopeBridge.upperSemicontinuous_of_complexTorusCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/94a37341-71d2-4347-8ad1-f3e9b1c225c5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauSlopeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauSlopeBridge
theorem _root_.solution
    {n : ℕ} (f : LogTorus n → ℝ)
    (hf : UpperSemicontinuous
      (fun z : LogSpace n =>
        f (complexTorusCoverProjection n z))) :
    UpperSemicontinuous f := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply (complexTorusCoverProjection_isOpenQuotientMap n).isQuotientMap.isOpen_preimage.mp
  change IsOpen
    ((fun z : LogSpace n =>
      f (complexTorusCoverProjection n z)) ⁻¹' Set.Iio a)
  exact hf.isOpen_preimage a
end Ehrhart.BergmanJetPortmanteauSlopeBridge
