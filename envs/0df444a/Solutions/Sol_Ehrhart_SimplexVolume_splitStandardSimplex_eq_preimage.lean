-- Prove2me | solution 1 for Ehrhart.SimplexVolume.splitStandardSimplex_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/c9b95efc-7cca-4f93-8dde-93c63b6f6a8e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution (n : ℕ) :
    splitStandardSimplex n =
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
          standardSimplex (n + 1) := by
  ext ⟨t, x⟩
  simp [splitStandardSimplex, standardSimplex,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.forall_fin_succ, Fin.sum_univ_succ, and_assoc]
end Ehrhart.SimplexVolume
