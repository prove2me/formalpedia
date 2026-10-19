-- Prove2me | solution 1 for Ehrhart.MonomialDivergence.one_le_abs_cast_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/ea269ce4-881d-4121-a8ec-8d048fdead44

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace Ehrhart.MonomialDivergence
theorem _root_.solution {i j : ℕ} (hij : i ≠ j) :
    (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hgt
    rw [abs_of_nonneg (by linarith)]
    linarith
end Ehrhart.MonomialDivergence
