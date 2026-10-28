-- Prove2me | solution 1 for D1Bound5.bennett_shifted_half_choose_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:28.565184+00:00
-- url     : https://prove2.me/submissions/5f03be49-5d8e-49e3-b551-01f21325757d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

private theorem bennett_real_factorial_mul_choose (s : ℝ) (h : ℕ) :
    (h.factorial : ℝ) * Ring.choose s h = (descPochhammer ℝ h).eval s := by
  have heq : (descPochhammer ℤ h).smeval s =
      (descPochhammer ℝ h).eval s := by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval,
      descPochhammer_eval_eq_ascPochhammer]
  have hh := Ring.descPochhammer_eq_factorial_smul_choose s h
  rw [heq, nsmul_eq_mul] at hh
  exact hh.symm

/-- All coefficients used by the local Taylor residue lie before the first
sign change. An ordinary degree-(k+1) binomial dominates them coefficientwise.
The small extra factor will be absorbed by the manuscript's rounding to H2. -/
theorem _root_.solution (k h : ℕ) (hh : h ≤ k) :
    |Ring.choose ((k : ℝ) + 1 / 2) h| ≤ (Nat.choose (k + 1) h : ℝ) := by
  have hh' : (h : ℝ) ≤ k := by exact_mod_cast hh
  have hlow : (h : ℝ) - 1 ≤ (k : ℝ) + 1 / 2 := by linarith
  have hhigh : (h : ℝ) - 1 ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hupper : (k : ℝ) + 1 / 2 ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hf : 0 < (h.factorial : ℝ) := by positivity
  have hnonneg := descPochhammer_nonneg hlow
  rw [← bennett_real_factorial_mul_choose] at hnonneg
  have hc : 0 ≤ Ring.choose ((k : ℝ) + 1 / 2) h := by nlinarith
  have hmono := (monotoneOn_descPochhammer_eval h) hlow hhigh hupper
  dsimp only at hmono
  rw [← bennett_real_factorial_mul_choose, ← bennett_real_factorial_mul_choose,
    Ring.choose_natCast] at hmono
  rw [abs_of_nonneg hc]
  exact (mul_le_mul_iff_of_pos_left hf).mp hmono













end D1Bound5
end
