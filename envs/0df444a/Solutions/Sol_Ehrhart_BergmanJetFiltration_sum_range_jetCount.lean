-- Prove2me | solution 1 for Ehrhart.BergmanJetFiltration.sum_range_jetCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/29d78962-bd0d-4664-8101-63099af50e85

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetFiltration
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.BergmanJetFiltration
theorem _root_.solution (n N : ℕ) :
    (∑ j ∈ Finset.range N, (n + j).choose n) =
      (n + N).choose (n + 1) := by
  cases N with
  | zero => simp
  | succ N =>
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.sum_range_add_choose N n
end Ehrhart.BergmanJetFiltration
