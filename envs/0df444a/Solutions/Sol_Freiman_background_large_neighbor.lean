-- Prove2me | solution 1 for Freiman.background_large_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T12:44:58.733955+00:00
-- url     : https://prove2.me/submissions/b8f2367e-6492-4501-931a-4614e8990dd0

import Definitions.Def_Freiman_backgroundWords

namespace LargeNeighborAux

open Freiman

private lemma cf_cons (a : ℕ+) (w : List ℕ+) :
    finiteCF (a :: w) = 1 / (((a : ℕ) : ℝ) + finiteCF w) := rfl

private lemma one_le (b : ℕ+) : (1:ℝ) ≤ ((b : ℕ) : ℝ) := by
  have : 1 ≤ (b : ℕ) := b.property
  exact_mod_cast this

private lemma nonneg (w : List ℕ+) : 0 ≤ finiteCF w := by
  induction w with
  | nil => simp [finiteCF]
  | cons a w ih =>
      rw [cf_cons]
      have h1 := one_le a
      exact le_of_lt (div_pos one_pos (by linarith))

private lemma le_one (w : List ℕ+) : finiteCF w ≤ 1 := by
  induction w with
  | nil => simp [finiteCF]
  | cons a w ih =>
      rw [cf_cons]
      have h1 := one_le a
      have h2 := nonneg w
      rw [div_le_one (by linarith)]
      linarith

private lemma cons_lower (b : ℕ+) (w : List ℕ+) :
    1 / (((b : ℕ) : ℝ) + 1) ≤ finiteCF (b :: w) := by
  rw [cf_cons]
  have h1 := one_le b
  have h2 := nonneg w
  have h3 := le_one w
  apply one_div_le_one_div_of_le
  · linarith
  · linarith

private lemma range_map_two (f : ℕ → ℕ+) (k : ℕ) :
    (List.range (k + 2)).map f
      = f 0 :: f 1 :: ((List.range k).map (fun j => f (j + 2))) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Uniform bound on the even convergents, depending only on the first two digits. -/
private lemma conv_le (f : ℕ → ℕ+) (n : ℕ) :
    cfConvergent f (2 * n) ≤ 1 / (((f 0 : ℕ) : ℝ) + 1 / (((f 1 : ℕ) : ℝ) + 1)) := by
  have hf0 := one_le (f 0)
  have hf1 := one_le (f 1)
  have hpos : 0 < 1 / (((f 1 : ℕ) : ℝ) + 1) := by positivity
  cases n with
  | zero =>
      have : cfConvergent f 0 = 0 := by norm_num [cfConvergent, finiteCF]
      rw [this]
      positivity
  | succ m =>
      have hEq : 2 * (m + 1) = 2 * m + 2 := by ring
      have hlow := cons_lower (f 1) ((List.range (2 * m)).map (fun j => f (j + 2)))
      unfold cfConvergent
      rw [hEq, range_map_two, cf_cons]
      apply one_div_le_one_div_of_le
      · linarith
      · linarith

/-- A tail whose leading digit is at least two has value below `1/2`. -/
lemma cfValue_lt_half (f : ℕ → ℕ+) (h : 2 ≤ (f 0 : ℕ)) : cfValue f < 1/2 := by
  have hf0 : (2:ℝ) ≤ ((f 0 : ℕ) : ℝ) := by exact_mod_cast h
  have hf1 := one_le (f 1)
  have hpos : 0 < 1 / (((f 1 : ℕ) : ℝ) + 1) := by positivity
  set C : ℝ := 1 / (((f 0 : ℕ) : ℝ) + 1 / (((f 1 : ℕ) : ℝ) + 1)) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hClt : C < 1/2 := by
    rw [hC, div_lt_iff₀ (by linarith)]
    linarith
  have hb : ∀ x ∈ Set.range (fun n : ℕ => cfConvergent f (2 * n)), x ≤ C := by
    rintro x ⟨n, rfl⟩; exact conv_le f n
  exact lt_of_le_of_lt (Real.sSup_le hb (le_of_lt hCpos)) hClt

/-- Every tail has value below `1`. -/
lemma cfValue_lt_one (f : ℕ → ℕ+) : cfValue f < 1 := by
  have hf0 := one_le (f 0)
  have hf1 := one_le (f 1)
  have hpos : 0 < 1 / (((f 1 : ℕ) : ℝ) + 1) := by positivity
  set C : ℝ := 1 / (((f 0 : ℕ) : ℝ) + 1 / (((f 1 : ℕ) : ℝ) + 1)) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hClt : C < 1 := by
    rw [hC, div_lt_one (by linarith)]
    linarith
  have hb : ∀ x ∈ Set.range (fun n : ℕ => cfConvergent f (2 * n)), x ≤ C := by
    rintro x ⟨n, rfl⟩; exact conv_le f n
  exact lt_of_le_of_lt (Real.sSup_le hb (le_of_lt hCpos)) hClt

end LargeNeighborAux

open LargeNeighborAux in
theorem solution (a : ℤ → ℕ+) (i : ℤ) (hi : (a i : ℕ) ≤ 3)
    (hn : 2 ≤ (a (i - 1) : ℕ) ∨ 2 ≤ (a (i + 1) : ℕ)) :
    Freiman.localValue a i < (9 / 2 : ℝ) := by
  have ha : ((a i : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hi
  unfold Freiman.localValue
  rcases hn with h | h
  · have hb : 2 ≤ ((fun n : ℕ => a (i - (n : ℤ) - 1)) 0 : ℕ) := by simpa using h
    have h1 := cfValue_lt_half (fun n : ℕ => a (i - (n : ℤ) - 1)) hb
    have h2 := cfValue_lt_one (fun n : ℕ => a (i + (n : ℤ) + 1))
    linarith
  · have hb : 2 ≤ ((fun n : ℕ => a (i + (n : ℤ) + 1)) 0 : ℕ) := by simpa using h
    have h1 := cfValue_lt_one (fun n : ℕ => a (i - (n : ℤ) - 1))
    have h2 := cfValue_lt_half (fun n : ℕ => a (i + (n : ℤ) + 1)) hb
    linarith
