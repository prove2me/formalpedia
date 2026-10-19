-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_tail_term_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/def96fd3-0485-441d-a2a0-ce3c626c2491

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1)
    (k : ℕ) :
    y ^ (m + k) / ((m + k).factorial : ℝ) ≤
      (y ^ m / (m.factorial : ℝ)) *
        ((1 / 2 : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hden : 0 < ((m + k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m + k + 1 by omega)
    have hdenlarge :
        (m : ℝ) + 1 ≤ ((m + k + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m + 1 ≤ m + k + 1 by omega)
    have hratio :
        y / ((m + k + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hstep :
        y ^ (m + (k + 1)) /
            ((m + (k + 1)).factorial : ℝ) =
          (y ^ (m + k) / ((m + k).factorial : ℝ)) *
            (y / ((m + k + 1 : ℕ) : ℝ)) := by
      rw [show m + (k + 1) = (m + k) + 1 by omega,
        Nat.factorial_succ, pow_succ]
      push_cast
      have hfact : ((m + k).factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (m + k)
      field_simp
    calc
      y ^ (m + (k + 1)) /
          ((m + (k + 1)).factorial : ℝ) =
        (y ^ (m + k) / ((m + k).factorial : ℝ)) *
          (y / ((m + k + 1 : ℕ) : ℝ)) := hstep
      _ ≤ ((y ^ m / (m.factorial : ℝ)) *
            ((1 / 2 : ℝ) ^ k)) * (1 / 2 : ℝ) := by
          exact mul_le_mul ih hratio
            (by positivity) (by positivity)
      _ = (y ^ m / (m.factorial : ℝ)) *
          ((1 / 2 : ℝ) ^ (k + 1)) := by
            rw [pow_succ]
            ring
end CohnElkies
