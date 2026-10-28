-- Prove2me | solution 1 for Erdos261.block_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:47:07.345919+00:00
-- url     : https://prove2.me/submissions/75e97acd-8c5a-4a71-ac64-7f676ddf4e63

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset


namespace E261A
open Finset

/-- A4 (Borwein–Loring block identity), for every `m` (including `m = 0, 1`). -/
theorem bl_block (m : ℕ) :
    ((2 ^ (m + 1) - m - 2 : ℕ) : ℚ) / 2 ^ (2 ^ (m + 1) - m - 2) =
      ∑ k ∈ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k := by
  set q := 2 ^ (m + 1) - m - 2 with hq
  have hm : m + 2 ≤ 2 ^ (m + 1) := by
    induction m with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have hq2 : (q : ℚ) + m + 2 = 2 ^ (m + 1) := by
    have : q + m + 2 = 2 ^ (m + 1) := by omega
    exact_mod_cast this
  have key : ∀ d : ℕ, ∑ k ∈ Ioc q (q + d), (k : ℚ) / 2 ^ k
      = (q + 2) / 2 ^ q - (q + d + 2) / 2 ^ (q + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [show q + (d+1) = (q + d) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
      push_cast
      rw [pow_succ]
      field_simp
      ring
  rw [key m, hq2, pow_add]
  field_simp
  ring

/-- A5 (block rewrite). If `S` represents `n` (i.e. `n/2^n = ∑_{k∈S} k/2^k`), contains
`q = 2^{m+1}-m-2` and misses the block `q+1, …, q+m`, then replacing `q` by the block gives
another representation of `n`, with `m - 1` more terms. -/
theorem block_rewrite (n m : ℕ) (S : Finset ℕ)
    (hS : (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k)
    (hq : 2 ^ (m + 1) - m - 2 ∈ S)
    (hdisj : Disjoint S (Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S.erase (2 ^ (m + 1) - m - 2) ∪
        Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k ∧
      #(S.erase (2 ^ (m + 1) - m - 2) ∪ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))
        + 1 = #S + m := by
  set q := 2 ^ (m + 1) - m - 2
  have hd : Disjoint (S.erase q) (Ioc q (q + m)) :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
  constructor
  · rw [Finset.sum_union hd, ← bl_block m, hS, ← Finset.add_sum_erase S _ hq]
    ring
  · rw [Finset.card_union_of_disjoint hd, Nat.card_Ioc, Finset.card_erase_of_mem hq]
    have : 0 < #S := Finset.card_pos.2 ⟨q, hq⟩
    omega

/-- A3 helper: the partial sums `P k = ∑_{1≤j≤k} c_j 2^{k-j}` along any `r` with
`2 r_j = c_j + r_{j+1}` satisfy `P k = r_1 2^k - r_{k+1}`. -/
lemma telescope (N : ℕ) (c r : ℕ → ℤ) (hr : ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1)) :
    ∀ k ≤ N, ∑ j ∈ Icc 1 k, c j * 2 ^ (k - j) = r 1 * 2 ^ k - r (k + 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, mul_one]
    have e : ∑ j ∈ Icc 1 k, c j * 2 ^ (k + 1 - j) = 2 * ∑ j ∈ Icc 1 k, c j * 2 ^ (k - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]; ring
    rw [e, ih']
    have := hr (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
    rw [pow_succ]
    linarith

/-- A3 (signed binary-carry formulation). For any integer column coefficients `c_1, …, c_N`,
`∑_{j=1}^N c_j 2^{N-j} = 0` iff there are integer carries `r` with `r_{N+1} = 0`, `r_1 = 0` and
`2 r_j = c_j + r_{j+1}` for `1 ≤ j ≤ N`. -/
theorem carry_iff (N : ℕ) (c : ℕ → ℤ) :
    ∑ j ∈ Icc 1 N, c j * 2 ^ (N - j) = 0 ↔
      ∃ r : ℕ → ℤ, r (N + 1) = 0 ∧ r 1 = 0 ∧ ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1) := by
  constructor
  · intro h
    -- forward definition: r 0 = r 1 = 0, r (j+1) = 2 r j - c j
    let r : ℕ → ℤ := fun j => Nat.rec (motive := fun _ => ℤ) 0
      (fun i ri => if i = 0 then 0 else 2 * ri - c i) j
    have r1 : r 1 = 0 := by simp [r]
    have rs : ∀ j, 1 ≤ j → r (j + 1) = 2 * r j - c j := by
      intro j hj
      show (if j = 0 then 0 else 2 * r j - c j) = _
      rw [if_neg (by omega)]
    have hr : ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1) := by
      intro j hj
      rw [rs j (Finset.mem_Icc.1 hj).1]; ring
    refine ⟨r, ?_, r1, hr⟩
    have := telescope N c r hr N le_rfl
    rw [h, r1] at this
    linarith
  · rintro ⟨r, hN, h1, hr⟩
    rw [telescope N c r hr N le_rfl, hN, h1]; ring

end E261A



namespace Erdos261

theorem block_rewrite (n m : ℕ) (S : Finset ℕ)
    (hS : (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k)
    (hq : 2 ^ (m + 1) - m - 2 ∈ S)
    (hdisj : Disjoint S (Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S.erase (2 ^ (m + 1) - m - 2) ∪
        Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k ∧
      #(S.erase (2 ^ (m + 1) - m - 2) ∪ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))
        + 1 = #S + m :=
  E261A.block_rewrite n m S hS hq hdisj

end Erdos261

open Erdos261 in
theorem solution (n m : ℕ) (S : Finset ℕ)
    (hS : (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k)
    (hq : 2 ^ (m + 1) - m - 2 ∈ S)
    (hdisj : Disjoint S (Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S.erase (2 ^ (m + 1) - m - 2) ∪
        Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k ∧
      #(S.erase (2 ^ (m + 1) - m - 2) ∪ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))
        + 1 = #S + m :=
  Erdos261.block_rewrite n m S hS hq hdisj

#print axioms solution
