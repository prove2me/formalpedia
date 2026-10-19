-- Prove2me | solution 1 for CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/bb715c8d-7309-4188-8b6f-b70c3a28bd1c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerWallisPhaseKernel_abs_le_moment
import Theorems.Thm_CohnElkies_lowerWallisRegularizedPhaseKernel_eq_add

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (hazero : 0 ≤ a) (haone : a ≤ 1)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤ |u| + 2 := by
  let q : ℝ := Real.exp (-t)
  let r : ℝ := Real.exp (-a * t)
  have hqpos : 0 < q := by
    try dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    try dsimp [q]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hrpos : 0 < r := by
    try dsimp [r]
    positivity
  have hrone : r ≤ 1 := by
    try dsimp [r]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hazero ht.le]
  have hqnonneg : 0 ≤ 1 - q := by linarith
  have hrnonneg : 0 ≤ 1 - r := by linarith
  have hqbound : 1 - q ≤ t := by
    try dsimp [q]
    linarith [Real.add_one_le_exp (-t)]
  have hrbound : 1 - r ≤ t := by
    have hfirst : 1 - r ≤ a * t := by
      try dsimp [r]
      linarith [Real.add_one_le_exp (-a * t)]
    have hsecond : a * t ≤ t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr haone) ht.le]
    exact hfirst.trans hsecond
  have hsq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hcorrection :
      |((1 - q) * (r - 1) * Real.cos (u * t)) /
          t ^ 2| ≤ 1 := by
    rw [abs_div, abs_of_pos hsq, abs_mul, abs_mul,
      abs_of_nonneg hqnonneg,
      abs_of_nonpos (show r - 1 ≤ 0 by linarith)]
    apply (div_le_iff₀ hsq).2
    have hcos := Real.abs_cos_le_one (u * t)
    calc
      (1 - q) * (-(r - 1)) * |Real.cos (u * t)| ≤
          (1 - q) * (1 - r) := by
        have hfactor : 0 ≤ (1 - q) * (1 - r) :=
          mul_nonneg hqnonneg hrnonneg
        nlinarith [mul_le_mul_of_nonneg_left hcos hfactor]
      _ ≤ t * t :=
        mul_le_mul hqbound hrbound hrnonneg ht.le
      _ = 1 * t ^ 2 := by ring
  rw [lowerWallisRegularizedPhaseKernel_eq_add]
  change
    |lowerWallisPhaseKernel u t +
      ((1 - q) * (r - 1) * Real.cos (u * t)) / t ^ 2| ≤
        |u| + 2
  calc
    |lowerWallisPhaseKernel u t +
        ((1 - q) * (r - 1) * Real.cos (u * t)) / t ^ 2| ≤
      |lowerWallisPhaseKernel u t| +
        |((1 - q) * (r - 1) * Real.cos (u * t)) /
          t ^ 2| := abs_add_le _ _
    _ ≤ (|u| + 1) + 1 :=
      add_le_add (lowerWallisPhaseKernel_abs_le_moment u ht)
        hcorrection
    _ = |u| + 2 := by ring
end CohnElkies
