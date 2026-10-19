-- Prove2me | solution 1 for CohnElkies.harmonic_halfIntegerGammaBoundary_abs_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/d8ee9d4d-77af-44c6-aba4-7be0035671cd

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger
import Theorems.Thm_CohnElkies_harmonic_abs_log_sqrtFactor_le_linear
import Theorems.Thm_CohnElkies_harmonic_abs_log_coth_div_le_linear

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
        |lowerGammaBoundaryLog
          ((k : ℝ) + 1 / 2) R x| ≤
          A * (1 + x) := by
  let S : ℝ :=
    ∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)
  let L : ℝ :=
    |((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2)|
  let Q : ℝ := |Real.log Real.pi|
  let A : ℝ :=
    L + S + (k : ℝ) + Real.pi + Q + 2
  have hS : 0 ≤ S := by
    try dsimp [S]
    positivity
  have hL : 0 ≤ L := abs_nonneg _
  have hQ : 0 ≤ Q := abs_nonneg _
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hsum :
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 +
              (x / 2) ^ 2))| ≤
        S + (k : ℝ) * x := by
    calc
      |∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 +
              (x / 2) ^ 2))| ≤
          ∑ j ∈ Finset.range k,
            |Real.log
              (Real.sqrt
                (((j : ℝ) + 1 / 2) ^ 2 +
                  (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k,
            ((j : ℝ) + 1 / 2 + x) := by
        apply Finset.sum_le_sum
        intro j hj
        apply harmonic_abs_log_sqrtFactor_le_linear
          (by positivity) hx
      _ = S + (k : ℝ) * x := by
        simp [S, Finset.sum_add_distrib]
  have hcorr :=
    harmonic_abs_log_coth_div_le_linear hx
  have hcorrhalf :
      |(1 / 2 : ℝ) *
        Real.log
          (lowerCoth (Real.pi * (x / 2)) /
            (x / 2))| ≤
        (1 / 2 : ℝ) *
          (Real.pi * x + Q + x) := by
    rw [abs_mul, abs_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Q] using! hcorr)
      (by norm_num)
  rw [lowerGammaBoundaryLog_halfInteger
    k R hxpos.ne']
  simp only [abs_of_pos hxpos]
  rw [show Real.pi * x / 2 =
    Real.pi * (x / 2) by ring]
  have hmain := abs_sub
    (((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2))
    (∑ j ∈ Finset.range k,
      Real.log
        (Real.sqrt
          (((j : ℝ) + 1 / 2) ^ 2 +
            (x / 2) ^ 2)))
  have htotal := abs_add_le
    (((k : ℝ) + 1 / 2) *
      Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 +
                (x / 2) ^ 2)))
    ((1 / 2 : ℝ) *
      Real.log
        (lowerCoth (Real.pi * (x / 2)) /
          (x / 2)))
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hxn : 0 ≤ x := hxpos.le
  try dsimp [A, L, Q]
  try dsimp [L] at hL
  try dsimp [Q] at hQ
  nlinarith [mul_nonneg hL hxn,
    mul_nonneg hS hxn,
    mul_nonneg hk hxn,
    mul_nonneg hπ hxn,
    mul_nonneg hQ hxn]
end CohnElkies
