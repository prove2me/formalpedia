-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.child_rate_average_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:36:30.729972+00:00
-- url     : https://prove2.me/submissions/afe4b0ab-1344-42dc-a568-7bcd09add56d

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_le_uniform
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_eq_count_mul_rateLeft
import Theorems.Thm_FD1D_V5_LocalPolicy_massRight_eq_count_mul_rateRight
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_pos
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_add_massRight
import Theorems.Thm_FD1D_V5_LocalPolicy_parentMass_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateLeft_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateRight_swap
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalPolicy
noncomputable section
private theorem ordered_child_rate_average_ge
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ≤ (rateLeft a p h x y + rateRight a p h x y) / 2 := by
  by_cases hzero : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [rateLeft, rateRight]
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := by omega
    have hb : bias a p h x 0 = parentMass h x 0 := by
      simp [bias, orderedBias, hxy, hx]
    have hleft : rateLeft a p h x 0 = h := by
      rw [rateLeft, if_neg hzero, if_neg hx]
      unfold massLeft
      rw [hb]
      simp [parentMass, inventory, hx]
    have hright : rateRight a p h x 0 = max h (p / a) := by
      rw [rateRight, if_neg hzero, if_pos rfl]
    rw [hleft, hright]
    linarith [le_max_left h (p / a)]
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hx : x ≠ 0 := by omega
    have hbU : bias a p h x y ≤ uniformCandidate h x y := by
      rw [bias, if_pos hxy]
      exact orderedBias_le_uniform hxy hypos
    have hN : 0 < inventory x y := inventory_pos hzero
    have hx' : 0 < (x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hx
    have hy' : 0 < (y : ℝ) := by exact_mod_cast hypos
    have hgap : 0 ≤ (x : ℝ) - y := by
      exact sub_nonneg.mpr (by exact_mod_cast hxy)
    have hbMul :
        bias a p h x y * inventory x y ≤
          parentMass h x y * ((x : ℝ) - y) := by
      unfold uniformCandidate at hbU
      exact (le_div_iff₀ hN).1 hbU
    have hmassL :
        (x : ℝ) * rateLeft a p h x y =
          massLeft a p h x y :=
      (massLeft_eq_count_mul_rateLeft a p h x y).symm
    have hmassR :
        (y : ℝ) * rateRight a p h x y =
          massRight a p h x y :=
      (massRight_eq_count_mul_rateRight a p h x y).symm
    have hweighted :
        (x : ℝ) * rateLeft a p h x y +
            (y : ℝ) * rateRight a p h x y =
          inventory x y * h := by
      rw [hmassL, hmassR, massLeft_add_massRight]
      rfl
    have hrateOrder :
        rateLeft a p h x y ≤ rateRight a p h x y := by
      have hid :
          2 * (x : ℝ) * y *
              (rateLeft a p h x y - rateRight a p h x y) =
            bias a p h x y * inventory x y -
              parentMass h x y * ((x : ℝ) - y) := by
        calc
          2 * (x : ℝ) * y *
              (rateLeft a p h x y - rateRight a p h x y) =
              2 * (y : ℝ) *
                  ((x : ℝ) * rateLeft a p h x y) -
                2 * (x : ℝ) *
                  ((y : ℝ) * rateRight a p h x y) := by ring
          _ = 2 * (y : ℝ) * massLeft a p h x y -
                2 * (x : ℝ) * massRight a p h x y := by
              rw [hmassL, hmassR]
          _ = bias a p h x y * inventory x y -
                parentMass h x y * ((x : ℝ) - y) := by
              unfold massLeft massRight inventory
              ring
      have hprod : 0 < 2 * (x : ℝ) * y := by positivity
      nlinarith
    have hproduct :
        0 ≤ ((x : ℝ) - y) *
          (rateRight a p h x y - rateLeft a p h x y) :=
      mul_nonneg hgap (sub_nonneg.mpr hrateOrder)
    unfold inventory at hweighted hN
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).2
    nlinarith
end
end FD1D.V5.LocalPolicy
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ≤ (rateLeft a p h x y + rateRight a p h x y) / 2 := by
  by_cases hxy : y ≤ x
  · exact ordered_child_rate_average_ge ha hp hh hxy ht
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    have htSwap :
        discrepancy a p h y x ≤ h / 2 := by
      simpa [discrepancy, parentMass_swap] using ht
    have hs := ordered_child_rate_average_ge ha hp hh hyx htSwap
    calc
      h ≤ (rateLeft a p h y x + rateRight a p h y x) / 2 := hs
      _ = (rateLeft a p h x y + rateRight a p h x y) / 2 := by
        rw [rateLeft_swap a p h x y, rateRight_swap a p h x y]
        ring
end FD1D.V5.LocalPolicy
