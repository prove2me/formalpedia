-- Prove2me | solution 1 for D1Bound5.bennett_shifted_half_tail_abs_Gamma
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:29:09.252706+00:00
-- url     : https://prove2.me/submissions/c381ac44-09bb-417a-8e81-18a0ed690fb8

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Theorems.Thm_D1Bound5_bennett_Gamma_half_add_nat
import Theorems.Thm_D1Bound5_bennett_ascPochhammer_half_pos
import Theorems.Thm_D1Bound5_bennett_factorial_mul_abs_choose
import Theorems.Thm_D1Bound5_bennett_negative_half_abs

section
open Polynomial

namespace D1Bound5







/-- The positive initial segment in the shifted-half descending product. -/
theorem bennett_shifted_half_initial_abs (k : ℕ) :
    ((k + 1).factorial : ℝ) * |Ring.choose ((k : ℝ) + 1 / 2) (k + 1)| =
      (ascPochhammer ℝ (k + 1)).eval (1 / 2) := by
  rw [bennett_factorial_mul_abs_choose, descPochhammer_eval_eq_ascPochhammer]
  have harg : ((k : ℝ) + 1 / 2) - ((k + 1 : ℕ) : ℝ) + 1 = 1 / 2 := by
    push_cast
    ring
  rw [harg, abs_of_pos (bennett_ascPochhammer_half_pos (k + 1))]



/-- Exact absolute Gamma formula after the positive part of a shifted
half-binomial coefficient. This is proved from finite choose identities,
factorials, and Gamma at positive half-integers, without reflection or a
contour representation. -/
theorem _root_.solution (k m : ℕ) :
    |Ring.choose ((k : ℝ) + 1 / 2) (k + 1 + m)| =
      Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma ((m : ℝ) + 1 / 2) /
        (Real.pi * Real.Gamma (((k + 1 + m : ℕ) : ℝ) + 1)) := by
  let n := k + 1 + m
  have hdiff : ((k : ℝ) + 1 / 2) - ((k + 1 : ℕ) : ℝ) = -1 / 2 := by
    push_cast
    ring
  have hchoose : ((n.choose (k + 1) : ℕ) : ℝ) *
      Ring.choose ((k : ℝ) + 1 / 2) n =
      Ring.choose ((k : ℝ) + 1 / 2) (k + 1) * Ring.choose (-1 / 2 : ℝ) m := by
    have h := Ring.choose_smul_choose (r := (k : ℝ) + 1 / 2)
      (n := n) (k := k + 1) (by dsimp [n]; omega)
    have hsub : n - (k + 1) = m := by dsimp [n]; omega
    simpa only [nsmul_eq_mul, hdiff, hsub] using h
  have habs := congrArg abs hchoose
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_mul] at habs
  have hfac : ((n.choose (k + 1) : ℕ) : ℝ) * ((k + 1).factorial : ℝ) *
      (m.factorial : ℝ) = (n.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := n) (k := k + 1) (by dsimp [n]; omega)
    have hsub : n - (k + 1) = m := by dsimp [n]; omega
    rw [hsub] at h
    exact_mod_cast h
  have hnum : (n.factorial : ℝ) * |Ring.choose ((k : ℝ) + 1 / 2) n| =
      (ascPochhammer ℝ (k + 1)).eval (1 / 2) *
        (ascPochhammer ℝ m).eval (1 / 2) := by
    calc
      _ = (((k + 1).factorial : ℝ) * |Ring.choose ((k : ℝ) + 1 / 2) (k + 1)|) *
          ((m.factorial : ℝ) * |Ring.choose (-1 / 2 : ℝ) m|) := by
        linear_combination
          (((k + 1).factorial : ℝ) * (m.factorial : ℝ)) * habs -
            |Ring.choose ((k : ℝ) + 1 / 2) n| * hfac
      _ = _ := by rw [bennett_shifted_half_initial_abs, bennett_negative_half_abs]
  have hG1 : Real.Gamma ((k : ℝ) + 3 / 2) = Real.Gamma (1 / 2 : ℝ) *
      (ascPochhammer ℝ (k + 1)).eval (1 / 2) := by
    have harg : (k : ℝ) + 3 / 2 = (1 / 2 : ℝ) + ((k + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [harg]
    exact bennett_Gamma_half_add_nat (k + 1)
  have hG2 : Real.Gamma ((m : ℝ) + 1 / 2) = Real.Gamma (1 / 2 : ℝ) *
      (ascPochhammer ℝ m).eval (1 / 2) := by
    simpa only [add_comm] using bennett_Gamma_half_add_nat m
  have hhalf : Real.Gamma (1 / 2 : ℝ) ^ 2 = Real.pi := by
    rw [Real.Gamma_one_half_eq]
    exact Real.sq_sqrt Real.pi_pos.le
  have hprod : Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma ((m : ℝ) + 1 / 2) =
      Real.pi * ((n.factorial : ℝ) * |Ring.choose ((k : ℝ) + 1 / 2) n|) := by
    rw [hG1, hG2, hnum]
    calc
      _ = Real.Gamma (1 / 2 : ℝ) ^ 2 *
          ((ascPochhammer ℝ (k + 1)).eval (1 / 2) *
            (ascPochhammer ℝ m).eval (1 / 2)) := by ring
      _ = _ := by rw [hhalf]
  have hden : Real.pi * Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (Real.Gamma_pos_of_pos (by positivity)).ne'
  change |Ring.choose ((k : ℝ) + 1 / 2) n| =
    Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma ((m : ℝ) + 1 / 2) /
      (Real.pi * Real.Gamma ((n : ℝ) + 1))
  apply (eq_div_iff hden).2
  rw [Real.Gamma_nat_eq_factorial]
  linear_combination -hprod



end D1Bound5
end
