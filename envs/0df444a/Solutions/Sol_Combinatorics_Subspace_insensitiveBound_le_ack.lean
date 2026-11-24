-- Prove2me | solution 1 for Combinatorics.Subspace.insensitiveBound_le_ack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:02.03664+00:00
-- url     : https://prove2.me/submissions/da8ab57e-9991-44d1-8364-29eb0d0e9d11

module
public import Mathlib.Computability.Ackermann
public import Definitions.Def_ShelahHalesJewett_HalesJewett
public import Definitions.Def_ShelahHalesJewett_Ackermann
section
@[expose] public section
namespace Combinatorics
private lemma pow_le_two_pow_ack_three {b x : ℕ} (hx : b ≤ x) : b ^ x ≤ 2 ^ ack 3 x := by
  apply (Nat.pow_le_pow_left (hx.trans Nat.lt_two_pow_self.le) x).trans
  rw [← pow_mul, ← sq]
  apply Nat.pow_le_pow_right two_pos
  exact (Nat.pow_le_pow_left (by grind [ack_zero]) 2).trans (ack_add_one_sq_lt_ack_add_three 0 x)
private lemma add_pow_le_ack_three {b x : ℕ} (hx : b ≤ x) : x + b ^ x ≤ ack 3 (ack 3 x) := by
  grind [pow_le_two_pow_ack_three hx, ack_three (ack 3 x), Nat.lt_two_pow_self (n := ack 3 x),
    lt_ack_right 3 x]
private lemma add_pow_pow_le_ack_four {b m : ℕ} (hb : 2 ≤ b) (hm : b ≤ ack 4 m) :
    ack 4 m + b ^ b ^ ack 4 m ≤ ack 4 (m + 4) := by
  rw [ack_succ_succ, ack_succ_succ, ack_succ_succ, ack_succ_succ]
  apply (ack_mono_right 3 (ack_mono_right 3 (add_pow_le_ack_three hm))).trans'
  apply (add_pow_le_ack_three (b := b) (x := ack 4 m + b ^ ack 4 m) (by grind)).trans'
  gcongr ?_ + b ^ ?_ <;> grind
namespace Subspace
private lemma insensitiveBound_pow_add_le_ack (k r i j : ℕ) :
    insensitiveBound k i (r ^ k ^ j) + j + i ≤ ack 4 (5 * i + j + k + r + 2) := by
  induction i generalizing j with
  | zero => grind [insensitiveBound, lt_ack_right 4 (5 * 0 + j + k + r + 2)]
  | succ i ih =>
    rw [insensitiveBound, ← pow_mul r, ← pow_succ, ← pow_mul, ← pow_add,
      (by grind : 5 * (i + 1) + j + k + r + 2 = 5 * i + (j + 1) + k + r + 2 + 4)]
    have h : r ^ k ^ (j + insensitiveBound k i (r ^ k ^ (j + 1))) ≤
        (k + r + 2) ^ (k + r + 2) ^ ack 4 (5 * i + (j + 1) + k + r + 2) := by
      gcongr <;> grind
    grind [add_pow_pow_le_ack_four (b := k + r + 2) (m := 5 * i + (j + 1) + k + r + 2) (by grind)
      (by grind [lt_ack_right 4 (5 * i + (j + 1) + k + r + 2)])]
end Subspace
namespace Line
variable {α κ ι : Type*} [Fintype α] [Fintype κ] [Fintype ι]
end Line
end Combinatorics
end
end

set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
open Combinatorics.Subspace
namespace Combinatorics.Subspace
theorem _root_.solution (k n r : ℕ) :
    insensitiveBound k n r ≤ ack 4 (5 * n + k + r + 2) := by
  grind [insensitiveBound_pow_add_le_ack k r n 0]
end Combinatorics.Subspace
