-- Prove2me | solution 1 for Ehrhart.SimplexVolume.normalizedVolume_standardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/2678dbdf-c273-4704-84bc-7677f5fe03c7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_standardSimplex_succ

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
    normalizedVolume (standardSimplex n) =
      1 / (n.factorial : ℝ) := by
  induction n with
  | zero =>
      have hz : (0 : Space 0) ∈ standardSimplex 0 := by
        simp [standardSimplex]
      unfold normalizedVolume
      rw [MeasureTheory.Measure.volume_pi_eq_dirac (0 : Space 0),
        MeasureTheory.Measure.dirac_apply_of_mem hz]
      simp
  | succ n ih =>
      rw [normalizedVolume_standardSimplex_succ n, ih,
        Nat.factorial_succ]
      push_cast
      have hfact : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hdenom : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
end Ehrhart.SimplexVolume
