-- Prove2me | solution 1 for CohnElkies.harmonic_integerGammaBoundary_abs_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/7b5f475a-4957-4f49-95aa-bdb6c3a6657d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer
import Theorems.Thm_CohnElkies_harmonic_abs_log_sqrtFactor_le_linear

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ x : ℝ, 2 ≤ x →
        |lowerGammaBoundaryLog (k : ℝ) R x| ≤
          A * (1 + x) := by
  let S : ℝ :=
    ∑ j ∈ Finset.range k, (j : ℝ)
  let L : ℝ :=
    |(k : ℝ) * Real.log (Real.pi * R ^ 2)|
  let A : ℝ := L + S + (k : ℝ) + 1
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hL : 0 ≤ L := abs_nonneg _
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro x hx
  have hxzero : x ≠ 0 := by linarith
  have hsum :
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))| ≤
        S + (k : ℝ) * x := by
    calc
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))| ≤
          ∑ j ∈ Finset.range k,
            |Real.log
              (Real.sqrt
                ((j : ℝ) ^ 2 + (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k,
            ((j : ℝ) + x) := by
        apply Finset.sum_le_sum
        intro j hj
        exact harmonic_abs_log_sqrtFactor_le_linear
          (Nat.cast_nonneg j) hx
      _ = S + (k : ℝ) * x := by
        simp [S, Finset.sum_add_distrib]
  rw [lowerGammaBoundaryLog_integer k R hxzero]
  have habs := abs_sub
    ((k : ℝ) * Real.log (Real.pi * R ^ 2))
    (∑ j ∈ Finset.range k,
      Real.log (Real.sqrt
        ((j : ℝ) ^ 2 + (x / 2) ^ 2)))
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hxpos : 0 ≤ x := by linarith
  try dsimp [A, L]
  try dsimp [L] at hL
  nlinarith [mul_nonneg hL hxpos,
    mul_nonneg hS hxpos, mul_nonneg hk hxpos]
end CohnElkies
