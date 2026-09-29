-- Prove2me | solution 1 for Freiman.form_root_data_of_cfValue
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:15:26.288395+00:00
-- url     : https://prove2.me/submissions/414312f8-7f08-4f74-87e9-5cd77b92d696

import Definitions.Def_Freiman_rootConvergentData
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_append
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_fibonacci_pair
import Theorems.Thm_Freiman_continuant_error_bound
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false

private theorem root_data_next (b : ℕ → ℕ+) (n : ℕ) :
    wordContinuantData ((List.range (n + 1)).map b) =
      ((continuantP b n, (b n : ℕ) * continuantP b n + continuantPrevP b n),
       (continuantQ b n, (b n : ℕ) * continuantQ b n + continuantPrevQ b n)) := by
  simp only [List.range_succ, List.map_append, List.map_singleton]
  exact continuant_append ((List.range n).map b) (b n)

private theorem root_data_previous (b : ℕ → ℕ+) (n : ℕ) :
    continuantPrevP b (n + 1) = continuantP b n ∧
      continuantPrevQ b (n + 1) = continuantQ b n := by
  constructor
  · exact congrArg (fun d : (ℕ × ℕ) × (ℕ × ℕ) => d.1.1) (root_data_next b n)
  · exact congrArg (fun d : (ℕ × ℕ) × (ℕ × ℕ) => d.2.1) (root_data_next b n)

private theorem root_data_growth (b : ℕ → ℕ+) (n : ℕ) :
    n ≤ continuantQ b n ∧ n ≤ continuantPrevQ b n + 1 := by
  have hp := continuant_fibonacci_pair ((List.range n).map b)
  change Nat.fib (((List.range n).map b).length) ≤ continuantPrevQ b n ∧
    Nat.fib (((List.range n).map b).length + 1) ≤ continuantQ b n at hp
  simp only [List.length_map, List.length_range] at hp
  have h₁ := Nat.le_fib_add_one n
  have h₂ := Nat.le_fib_add_one (n + 1)
  omega

theorem solution (b : ℕ → ℕ+) (z : ℤ) :
    Nonempty (RootConvergentData (cfValue b + (z : ℝ))) := by
  let p : ℕ → ℤ := fun n => (continuantP b n : ℤ) + z * (continuantQ b n : ℤ)
  let τ : ℕ → ℝ := fun n => cfValue (fun k => b (n + 1 + k))
  have hτpos (n : ℕ) : 0 < τ n := (cf_convergence _).2.2.1
  have hτlt (n : ℕ) : τ n < 1 := (cf_convergence _).2.2.2.1
  have hqpos (n : ℕ) : 0 < continuantQ b n :=
    continuant_denominator_pos ((List.range n).map b)
  have hqreal (n : ℕ) : 0 < (continuantQ b n : ℝ) := by
    exact_mod_cast hqpos n
  refine ⟨{
    p := p
    q := continuantQ b
    complete := fun n => 1 / τ n
    q_pos := hqpos
    det := ?_
    complete_gt := ?_
    complete_irr := ?_
    root_identity := ?_
    error_zero := ?_
    denominator_difference_escape := ?_
  }⟩
  · intro n
    have hd := continuant_determinant ((List.range (n + 1)).map b)
    change (continuantPrevP b (n + 1) : ℤ) * continuantQ b (n + 1) -
      (continuantP b (n + 1) : ℤ) * continuantPrevQ b (n + 1) = _ at hd
    rw [(root_data_previous b n).1, (root_data_previous b n).2] at hd
    have habs : |(continuantP b (n + 1) : ℤ) * continuantQ b n -
        (continuantP b n : ℤ) * continuantQ b (n + 1)| = 1 := by
      rw [show (continuantP b (n + 1) : ℤ) * continuantQ b n -
          (continuantP b n : ℤ) * continuantQ b (n + 1) =
          -((continuantP b n : ℤ) * continuantQ b (n + 1) -
            (continuantP b (n + 1) : ℤ) * continuantQ b n) by ring,
        hd, abs_neg, abs_pow]
      norm_num
    have heq : p (n + 1) * (continuantQ b n : ℤ) -
        p n * (continuantQ b (n + 1) : ℤ) =
        (continuantP b (n + 1) : ℤ) * continuantQ b n -
          (continuantP b n : ℤ) * continuantQ b (n + 1) := by
      dsimp [p]
      ring
    change p (n + 1) * (continuantQ b n : ℤ) - p n * (continuantQ b (n + 1) : ℤ) = 1 ∨
      p (n + 1) * (continuantQ b n : ℤ) - p n * (continuantQ b (n + 1) : ℤ) = -1
    rw [heq]
    exact (abs_eq (show (0 : ℤ) ≤ 1 by norm_num)).mp habs
  · intro n
    exact (lt_div_iff₀ (hτpos n)).2 (by simpa only [one_mul] using hτlt n)
  · intro n
    simpa only [one_div] using ((cf_convergence (fun k => b (n + 1 + k))).2.1).inv
  · intro n
    have hv : cfValue b =
        ((continuantP b (n + 1) : ℝ) + τ n * continuantP b n) /
        ((continuantQ b (n + 1) : ℝ) + τ n * continuantQ b n) := by
      rw [cfValue_prefix b (n + 1)]
      have hm := prefixEval_mobius ((List.range (n + 1)).map b) (τ n) (hτpos n).le
      change prefixEval ((List.range (n + 1)).map b) (τ n) =
        ((continuantP b (n + 1) : ℝ) + τ n * continuantPrevP b (n + 1)) /
        ((continuantQ b (n + 1) : ℝ) + τ n * continuantPrevQ b (n + 1)) at hm
      simpa only [(root_data_previous b n).1, (root_data_previous b n).2] using hm
    have ht : τ n ≠ 0 := ne_of_gt (hτpos n)
    have hd : (continuantQ b (n + 1) : ℝ) + τ n * continuantQ b n ≠ 0 := by
      have hq := hqreal (n + 1)
      have hτ := hτpos n
      positivity
    have hd' : (continuantQ b (n + 1) : ℝ) * (1 / τ n) + continuantQ b n ≠ 0 := by
      have hq := hqreal (n + 1)
      have hτ := hτpos n
      positivity
    simp only [p, Int.cast_add, Int.cast_natCast, Int.cast_mul]
    rw [hv]
    field_simp
    ring
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hNq : (N : ℝ) ≤ (continuantQ b (n + 1) : ℝ) := by
      exact_mod_cast (hn.trans ((Nat.le_succ n).trans (root_data_growth b (n + 1)).1))
    have hmul : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hbound : 1 / (continuantQ b (n + 1) : ℝ) < ε := by
      apply (div_lt_iff₀ (hqreal (n + 1))).2
      nlinarith
    have heq : (p n : ℝ) - (cfValue b + (z : ℝ)) * continuantQ b n =
        -((continuantQ b n : ℝ) * cfValue b - continuantP b n) := by
      simp only [p, Int.cast_add, Int.cast_natCast, Int.cast_mul]
      ring
    rw [heq, abs_neg]
    exact (continuant_error_bound b n).trans hbound
  · intro R
    obtain ⟨N, hN⟩ := exists_nat_gt (R + 1)
    refine ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hprev : (n : ℝ) ≤ (continuantPrevQ b n : ℝ) + 1 := by
      exact_mod_cast (root_data_growth b n).2
    have hnext : (continuantQ b (n + 1) : ℝ) =
        ((b n : ℕ) : ℝ) * continuantQ b n + continuantPrevQ b n := by
      exact_mod_cast congrArg (fun d : (ℕ × ℕ) × (ℕ × ℕ) => d.2.2) (root_data_next b n)
    have ha : (1 : ℝ) ≤ ((b n : ℕ) : ℝ) := by exact_mod_cast (b n).pos
    have hm := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (continuantQ b n) :
      (0 : ℝ) ≤ (continuantQ b n : ℝ))
    nlinarith
