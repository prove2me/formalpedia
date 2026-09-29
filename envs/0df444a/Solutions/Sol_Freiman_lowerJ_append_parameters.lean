-- Prove2me | solution 1 for Freiman.lowerJ_append_parameters
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:03:04.884067+00:00
-- url     : https://prove2.me/submissions/394b2c6e-5ae1-410d-a776-864668bff097

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

/- Continuant algebra for `lowerCD`.
`lowerCD w` folds `(x,y) |-> (y, x + a*y)` from `(0,1)`.  Because the fold body
ascribes `(a : Nat)` without pinning the binder, Lean elaborates it over a coerced
digit list; `lowerCD_eq` bridges that to a plain fold over `List Nat`, and the rest
of the development works with the un-coerced `cdL`. -/

private def cdL (init : ℕ × ℕ) (l : List ℕ) : ℕ × ℕ :=
  l.foldl (fun z a => (z.2, z.1 + a * z.2)) init

private lemma lowerCD_eq (w : List ℕ+) :
    lowerCD w = cdL (0, 1) (w.map (fun a : ℕ+ => (a : ℕ))) := by
  simp only [lowerCD, cdL]
  simp [← List.map_eq_flatMap]

private lemma cdL_append (init : ℕ × ℕ) (l₁ l₂ : List ℕ) :
    cdL init (l₁ ++ l₂) = cdL (cdL init l₁) l₂ := by
  simp only [cdL, List.foldl_append]

private lemma cdL_cons (init : ℕ × ℕ) (a : ℕ) (l : List ℕ) :
    cdL init (a :: l) = cdL (init.2, init.1 + a * init.2) l := rfl

private lemma cdL_snoc (init : ℕ × ℕ) (l : List ℕ) (n : ℕ) :
    cdL init (l ++ [n]) = ((cdL init l).2, (cdL init l).1 + n * (cdL init l).2) := by
  simp only [cdL, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma map_replicate_three (k : ℕ) :
    List.map (fun a : ℕ+ => (a : ℕ)) (List.replicate k 3) = List.replicate k 3 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.map_cons, ih, List.replicate_succ]
      norm_num

private lemma cdL_snd_pos (init : ℕ × ℕ) (l : List ℕ) (h0 : 0 < init.2)
    (hl : ∀ n ∈ l, 0 < n) : 0 < (cdL init l).2 := by
  induction l generalizing init with
  | nil => simpa [cdL] using h0
  | cons a l ih =>
      have ha : 0 < a := hl a (List.mem_cons_self ..)
      have h1 : 0 < init.1 + a * init.2 := by
        have := Nat.mul_pos ha h0
        omega
      exact ih (init := (init.2, init.1 + a * init.2)) h1
        (fun n hn => hl n (List.mem_cons_of_mem a hn))

private lemma lowerCD_snd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  rw [lowerCD_eq]
  exact cdL_snd_pos (0, 1) _ (by norm_num)
    (fun n hn => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hn
      exact a.2)

private lemma lowerCD_snoc (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a])
      = ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  simp only [lowerCD_eq, List.map_append, List.map_singleton, List.nil_append, cdL_snoc]

private lemma lowerRatio_snoc (w : List ℕ+) (a : ℕ+) :
    lowerRatio (w ++ [a]) = 1 / ((a : ℝ) + lowerRatio w) := by
  have hQ : (((lowerCD w).2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lowerCD_snd_pos w))
  rw [lowerRatio, lowerCD_snoc, lowerRatio]
  push_cast
  field_simp
  ring

private lemma prefixEval_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private lemma finiteCF_eq_prefixEval (w : List ℕ+) : finiteCF w = prefixEval w 0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [finiteCF, prefixEval, ih]

private lemma lowerRatio_reverse (w : List ℕ+) : lowerRatio w.reverse = prefixEval w 0 := by
  induction w with
  | nil => norm_num [lowerRatio, lowerCD, prefixEval]
  | cons a t ih => rw [List.reverse_cons, lowerRatio_snoc, ih, prefixEval]

private lemma lowerRatio_eq_prefixEval_reverse (w : List ℕ+) :
    lowerRatio w = prefixEval w.reverse 0 := by
  have h := lowerRatio_reverse w.reverse
  rwa [List.reverse_reverse] at h

private lemma lowerRatio_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w := by
  rw [lowerRatio]
  exact div_nonneg (by positivity) (by positivity)

/- The run sequence `dseq`: continuants of `List.replicate k 3`. -/

private def dseq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * dseq (n + 1) + dseq n

private lemma dseq_ss (n : ℕ) : dseq (n + 2) = 3 * dseq (n + 1) + dseq n := rfl

private lemma dseq_pos_succ (k : ℕ) : 0 < dseq (k + 1) := by
  induction k with
  | zero => norm_num [dseq]
  | succ k ih =>
      rw [dseq_ss]
      have : 0 < 3 * dseq (k + 1) := Nat.mul_pos (by norm_num) ih
      omega

private lemma cdL_run_succ (init : ℕ × ℕ) (k : ℕ) :
    cdL init (List.replicate (k + 1) 3) =
      (dseq k * init.1 + dseq (k + 1) * init.2,
        dseq (k + 1) * init.1 + dseq (k + 2) * init.2) := by
  induction k generalizing init with
  | zero =>
      cases init with
      | mk a b =>
          simp only [List.replicate_succ, List.replicate_zero, cdL, List.foldl_cons,
            List.foldl_nil, dseq]
          ring
  | succ k ih =>
      rw [List.replicate_succ, cdL_cons]
      cases init with
      | mk a b =>
          rw [ih (b, a + 3 * b)]
          -- `simp only` (unlike `rw`) does not fail when a pattern is absent, so this
          -- closes the step whichever way Lean prints the recursive index
          -- (`1 + k` vs `k + 1`, and `k + 1 + 1` vs `k + 2`).
          -- `dsimp only` discharges the `Prod` projections by iota reduction, which
          -- avoids depending on a named `Prod.fst_mk` lemma (it lives in the `Omega`
          -- namespace, not under `Prod`).
          dsimp only
          simp only [dseq_ss k, dseq_ss (k + 1)]
          ring

private lemma lowerCD_run_pair (k : ℕ) :
    lowerCD (List.replicate k 3) = (dseq k, dseq (k + 1)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [lowerCD, dseq]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    rw [lowerCD_eq, map_replicate_three, cdL_run_succ (0, 1) j]
    simp only [dseq]
    have h1 : j + 1 = j.succ := by omega
    simp only [h1]
    ring

private lemma lowerCD_run_fst (k : ℕ) : (lowerCD (List.replicate k 3)).1 = dseq k := by
  rw [lowerCD_run_pair k]

private lemma lowerCD_run_snd (k : ℕ) : (lowerCD (List.replicate k 3)).2 = dseq (k + 1) := by
  rw [lowerCD_run_pair k]

private lemma lowerJTau_eq (k : ℕ) :
    lowerJTau k = (dseq k : ℝ) / (dseq (k + 1) : ℝ) := by
  rw [lowerJTau, finiteCF_eq_prefixEval, ← lowerRatio_reverse, List.reverse_replicate,
    lowerRatio, lowerCD_run_fst k, lowerCD_run_snd k]
  <;> push_cast
  <;> ring

private lemma lowerJTau_nonneg (k : ℕ) : 0 ≤ lowerJTau k := by
  rw [lowerJTau_eq]
  exact div_nonneg (by positivity) (by positivity)

/- The second continuant after appending a run of threes. -/

private lemma lowerCD_run_append_snd (u : List ℕ+) (k : ℕ) :
    (lowerCD (u ++ List.replicate k 3)).2
      = (lowerCD u).2 * dseq (k + 1) + (lowerCD u).1 * dseq k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [lowerCD, dseq]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    rw [lowerCD_eq, List.map_append, cdL_append, ← lowerCD_eq, map_replicate_three j.succ,
      cdL_run_succ (lowerCD u) j]
    have h1 : j + 1 = j.succ := by omega
    have h2 : j + 2 = j.succ + 1 := by omega
    simp only [h1, h2]
    ring

private lemma lowerCD_run_factor (u : List ℕ+) (k : ℕ) :
    (((lowerCD (u ++ List.replicate k 3)).2 : ℕ) : ℝ)
      = (((lowerCD u).2 : ℕ) : ℝ) * ((dseq (k + 1) : ℕ) : ℝ)
        * (1 + lowerRatio u * lowerJTau k) := by
  have hQ : (((lowerCD u).2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lowerCD_snd_pos u))
  have hd : ((dseq (k + 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (dseq_pos_succ k))
  rw [lowerCD_run_append_snd u k, lowerRatio, lowerJTau_eq]
  <;> push_cast
  <;> field_simp
  <;> ring

private lemma lowerScale_run (u v : List ℕ+) (k : ℕ) :
    lowerScale (u ++ List.replicate k 3, v ++ List.replicate k 3)
      = lowerScale (u, v)
        * ((1 + lowerRatio u * lowerJTau k) ^ 2 / (1 + lowerRatio v * lowerJTau k) ^ 2) := by
  have hC : ((dseq (k + 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (dseq_pos_succ k))
  have hDu : 1 + lowerRatio u * lowerJTau k ≠ 0 := by
    nlinarith [mul_nonneg (lowerRatio_nonneg u) (lowerJTau_nonneg k)]
  have hDv : 1 + lowerRatio v * lowerJTau k ≠ 0 := by
    nlinarith [mul_nonneg (lowerRatio_nonneg v) (lowerJTau_nonneg k)]
  rw [lowerScale, lowerScale, lowerCD_run_factor u k, lowerCD_run_factor v k]
  <;> field_simp
  <;> ring

theorem solution (p : LowerPair) (k : ℕ) : lowerJUpdated p k := by
  unfold lowerJUpdated
  refine ⟨?_, ?_, ?_⟩
  · rw [lowerJIter, lowerRatio_eq_prefixEval_reverse, List.reverse_append,
      List.reverse_replicate, prefixEval_append, ← lowerRatio_eq_prefixEval_reverse]
  · rw [lowerJIter, lowerRatio_eq_prefixEval_reverse, List.reverse_append,
      List.reverse_replicate, prefixEval_append, ← lowerRatio_eq_prefixEval_reverse]
  · rw [lowerScale_run, lowerJQ]
    <;> field_simp
    <;> ring
