-- Prove2me | solution 1 for CompactnessConjecture.finite_heavy_fiber_mass_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/419773d6-73b1-48e9-80fc-9399108f6555

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ)
    (hN : 0 < N)
    (hcapacity : Fintype.card α ≤ N)
    (htotal : p ≤ ∑ x : α, weight x) :
    (p : ℝ) / 2 ≤ finiteHeavyFiberMass weight N p := by
  classical
  let R : ℝ := fourPathHeavyThreshold N p
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hsum :
      (∑ x : α, (weight x : ℝ)) ≤
        (∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) +
          (Fintype.card α : ℝ) * R := by
    calc
      (∑ x : α, (weight x : ℝ)) ≤
          ∑ x : α,
            ((if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) + R) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · linarith
        · have : (weight x : ℝ) < R := lt_of_not_ge hx
          linarith
      _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hcapacityReal : (Fintype.card α : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcapacity
  have hthreshold : (N : ℝ) * R = (p : ℝ) / 2 := by
    dsimp [R, fourPathHeavyThreshold]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  have htotalReal :
      (p : ℝ) ≤ ∑ x : α, (weight x : ℝ) := by
    exact_mod_cast htotal
  change (p : ℝ) / 2 ≤
    ∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0
  nlinarith [mul_le_mul_of_nonneg_right hcapacityReal hR]
end CompactnessConjecture
