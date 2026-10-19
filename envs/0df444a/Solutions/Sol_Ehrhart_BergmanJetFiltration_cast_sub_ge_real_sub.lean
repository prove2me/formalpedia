-- Prove2me | solution 1 for Ehrhart.BergmanJetFiltration.cast_sub_ge_real_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/ef959c4e-613b-4621-9f31-8f4650d50c74

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
theorem _root_.solution (a b : ℕ) :
    (a : ℝ) - (b : ℝ) ≤ ((a - b : ℕ) : ℝ) := by
  exact sub_le_iff_le_add.mpr
    (by exact_mod_cast (show a ≤ a - b + b from le_tsub_add))
end Ehrhart.BergmanJetFiltration
