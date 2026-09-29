-- Prove2me | solution 1 for Esgk.high_ratio_factor_exists
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:48:17.662097+00:00
-- url     : https://prove2.me/submissions/2630351c-4afc-4b95-8102-70bf4bfb11f8

/-
Standalone solution artifact for Prove2me (mirrors esgk-on3
lean/Esgk/AdditiveExcessArithmetic.lean).-/

import Mathlib

/-- Factor selection (§15, boxed (15.1)): from total counts and total
degree, some factor has high point-to-degree ratio. With `∑ N = n` and
`∑ d ≤ 2s`, some `i` satisfies `d i ≤ 2s` and `n * d i ≤ N i * (2s)`. -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (N d : ι → ℕ) (n s : ℕ) (hn : 1 ≤ n)
    (hN : ∑ i, N i = n) (hd : ∑ i, d i ≤ 2 * s) :
    ∃ i, d i ≤ 2 * s ∧ n * d i ≤ N i * (2 * s) := by
  have hdi : ∀ i, d i ≤ 2 * s := fun i =>
    le_trans
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (d j))
        (Finset.mem_univ i)) hd
  by_contra hcon
  have h1 : ∀ i, N i * (2 * s) + 1 ≤ n * d i := by
    intro i
    have h2 : ¬ n * d i ≤ N i * (2 * s) := fun hle => hcon ⟨i, hdi i, hle⟩
    omega
  have hsum : ∑ i, (N i * (2 * s) + 1) ≤ ∑ i, n * d i :=
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one, hN, Finset.card_univ,
    Nat.cast_id] at hsum
  have hle : n * (∑ i, d i) ≤ n * (2 * s) :=
    mul_le_mul_of_nonneg_left hd (Nat.zero_le _)
  have hcard0 : Fintype.card ι = 0 := by omega
  have hempty : (Finset.univ : Finset ι) = ∅ :=
    Finset.card_eq_zero.mp (by rwa [Finset.card_univ])
  rw [hempty] at hN
  simp at hN
  omega


