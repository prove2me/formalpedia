-- Prove2me | solution 1 for Ehrhart.JetCounting.card_jetIndexLT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/cefd2555-88ac-4c4d-b1aa-7e0dd5a1b369

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetCounting
open scoped BigOperators
namespace Ehrhart.JetCounting
theorem _root_.solution (n j : ℕ) (hj : 0 < j) :
    Fintype.card (JetIndexLT n j) = (n + j - 1).choose n := by
  rw [← Fintype.card_congr (symSigmaEquivJetIndexLT n j), Fintype.card_sigma]
  simp_rw [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]
  have hsum := Nat.sum_range_multichoose (j - 1) n
  rw [Nat.sub_add_cancel hj] at hsum
  convert hsum using 1
  congr 1
  omega
end Ehrhart.JetCounting
