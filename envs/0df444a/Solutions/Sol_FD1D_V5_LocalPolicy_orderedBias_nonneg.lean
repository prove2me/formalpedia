-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.orderedBias_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:42.782881+00:00
-- url     : https://prove2.me/submissions/644b3a71-2332-45fd-b297-8c038fe0763f

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_parent_interval_bound
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_nonneg
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_pos
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalPolicy
noncomputable section
private theorem orderedBias_eq_caps
    {a p h : ℝ} {x y : ℕ}
    (hxy : y < x) (hy : 0 < y) :
    orderedBias a p h x y =
      min (feedbackCandidate a h x y)
        (min (uniformCandidate h x y) (floorCandidate a p h x y)) := by
  unfold orderedBias
  rw [if_neg (by omega : x ≠ y)]
  rw [if_neg (by omega : x + y ≠ 0)]
  rw [if_neg (by omega : y ≠ 0)]
private theorem feedbackCandidate_nonneg
    {a h : ℝ} {x y : ℕ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hxy : y ≤ x) (hy : 0 < y) :
    0 ≤ feedbackCandidate a h x y := by
  have hx : 0 < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le hy hxy
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 ≤ inventory x y := inventory_nonneg x y
  have hgap : 0 ≤ (x : ℝ) - y := by
    exact sub_nonneg.mpr (by exact_mod_cast hxy)
  unfold feedbackCandidate parentMass
  positivity
private theorem uniformCandidate_nonneg
    {h : ℝ} {x y : ℕ}
    (hh : 0 ≤ h) (hxy : y ≤ x) (hy : 0 < y) :
    0 ≤ uniformCandidate h x y := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hgap : 0 ≤ (x : ℝ) - y := by
    exact sub_nonneg.mpr (by exact_mod_cast hxy)
  unfold uniformCandidate parentMass
  positivity
private theorem floorCandidate_pos
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 < floorCandidate a p h x y := by
  have hx : 0 < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le hy hxy
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hden : 0 < 2 * (y : ℝ) + a := by positivity
  have hp := parent_interval_bound ha ht
  unfold floorCandidate parentMass inventory at *
  apply sub_pos.mpr
  apply (div_lt_iff₀ hden).2
  nlinarith [mul_pos ha (mul_pos hh hx)]
end
end FD1D.V5.LocalPolicy
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ orderedBias a p h x y := by
  by_cases heq : x = y
  · simp [orderedBias, heq]
  have hlt : y < x := lt_of_le_of_ne hxy (Ne.symm heq)
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by omega
    simp [orderedBias, hx, parentMass, inventory, hh.le]
    positivity
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    rw [orderedBias_eq_caps hlt hypos]
    apply le_min
    · exact feedbackCandidate_nonneg ha.le hh.le hxy hypos
    · apply le_min
      · exact uniformCandidate_nonneg hh.le hxy hypos
      · exact (floorCandidate_pos ha hh hxy hypos ht).le
end FD1D.V5.LocalPolicy
