-- Prove2me | solution 1 for GRH.conductors_three_four_low_height_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:06:11.802848+00:00
-- url     : https://prove2.me/submissions/a65773cc-4f2a-44a2-ad9a-066621ab4c38

import Theorems.Thm_GRH_dirichlet_low_height_nonzero_of_nonnegative_real_prefixes
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

open Complex

private lemma period_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range q, (χ ((n+i+1:ℕ) : ZMod q)).re = 0 := by
  have reindex (f : ZMod q → ℂ) :
      ∑ i ∈ Finset.range q, f (i : ZMod q) = ∑ b : ZMod q, f b := by
    refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun b => b.val)
      (fun _ _ => Finset.mem_univ _) (fun b _ => Finset.mem_range.mpr (ZMod.val_lt b))
      (fun _ hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
      (fun b _ => ZMod.natCast_rightInverse b) (fun _ _ => rfl)
  have eq : ∑ i ∈ Finset.range q, χ ((n+i+1:ℕ) : ZMod q) = 0 := by
    calc _ = ∑ i ∈ Finset.range q, (fun b : ZMod q => χ ((n+1:ℕ)+b)) i := by
            apply Finset.sum_congr rfl
            intro i _
            push_cast
            congr 1
            abel
         _ = ∑ b : ZMod q, χ ((n+1:ℕ)+b) := reindex (fun b : ZMod q => χ ((n+1:ℕ)+b))
         _ = ∑ b : ZMod q, χ b := Fintype.sum_equiv (Equiv.addLeft ((n+1:ℕ) : ZMod q)) _ _ (fun _ => rfl)
         _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re eq

private lemma reduce_period {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (small : ∀ n < q, 0 ≤ ∑ k ∈ Finset.range n, (χ ((k+1:ℕ) : ZMod q)).re) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range n, (χ ((k+1:ℕ) : ZMod q)).re := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · exact small n hn
    · have add : n-q+q=n := Nat.sub_add_cancel (le_of_not_gt hn)
      have prev := ih (n-q) (Nat.sub_lt (lt_of_lt_of_le (NeZero.pos q) (le_of_not_gt hn)) (NeZero.pos q))
      conv_rhs => rw [← add, Finset.sum_range_add]
      simpa only [period_sum χ hχ, add_zero] using prev

theorem solution (q : ℕ) [NeZero q] (hq : q = 3 ∨ q = 4)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ)
    (ha : (1/2:ℝ) ≤ z.re) (hb : z.re ≤ 1) (ht : |z.im| ≤ 1/(256*(q:ℝ))) :
    χ.LFunction z ≠ 0 := by
  apply GRH.dirichlet_low_height_nonzero_of_nonnegative_real_prefixes q χ hχ _ z ha hb ht
  apply reduce_period χ hχ
  have lo (a : ZMod q) : -(1:ℝ) ≤ (χ a).re :=
    (abs_le.mp ((abs_re_le_norm _).trans (χ.norm_le_one a))).1
  rcases hq with rfl | rfl
  · intro n hn
    interval_cases n <;> norm_num [Finset.sum_range_succ]
    linarith [lo 2]
  · have h2 : χ (2 : ZMod 4) = 0 := MulChar.map_nonunit χ (by decide)
    intro n hn
    interval_cases n <;> norm_num [Finset.sum_range_succ,h2]
    linarith [lo 3]
