-- Prove2me | solution 1 for Ehrhart.BergmanJetFiltration.real_jetLayercake_le_nat_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/902cdac0-2a86-4001-b907-718f5b912cce

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetFiltration_sum_range_jetCount
import Theorems.Thm_Ehrhart_BergmanJetFiltration_cast_sub_ge_real_sub

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
theorem _root_.solution (n d N : ℕ) :
    (N : ℝ) * (d : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.range N,
        (d - (n + j).choose n)) : ℕ) := by
  calc
    (N : ℝ) * (d : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) =
      ∑ j ∈ Finset.range N,
        ((d : ℝ) - (((n + j).choose n : ℕ) : ℝ)) := by
          rw [Finset.sum_sub_distrib]
          simp [← Nat.cast_sum, sum_range_jetCount]
    _ ≤ ∑ j ∈ Finset.range N,
          ((d - (n + j).choose n : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          exact cast_sub_ge_real_sub d ((n + j).choose n)
    _ = ((∑ j ∈ Finset.range N,
          (d - (n + j).choose n)) : ℕ) := by
          simp
end Ehrhart.BergmanJetFiltration
