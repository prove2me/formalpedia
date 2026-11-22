-- Prove2me | solution 1 for Egrs75.LeafInduction.seed_lowDigits_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:58.716983+00:00
-- url     : https://prove2.me/submissions/b17d32b6-882a-480a-ad38-c40272bf3284

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75
namespace Egrs75.LeafInduction
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (k : ℕ) : LowDigits p (p ^ k) := by
  have hp1 : 1 < p := by omega
  unfold LowDigits
  intro d hd
  have hk : Nat.digits p (p ^ k) = List.replicate k 0 ++ Nat.digits p 1 := by
    have := Nat.digits_base_pow_mul (b := p) (k := k) (m := 1) hp1 (by norm_num)
    simpa using this
  rw [hk, List.mem_append] at hd
  rcases hd with hd | hd
  · rw [List.mem_replicate] at hd; omega
  · rw [Nat.digits_of_lt p 1 (by norm_num) (by omega)] at hd
    simp only [List.mem_singleton] at hd
    rw [hd]
    -- `1 ≤ (p-1)/2` since `p ≥ 3`
    have : 2 ≤ p - 1 := by omega
    calc (1 : ℕ) = 2 / 2 := by norm_num
      _ ≤ (p - 1) / 2 := Nat.div_le_div_right this
end Egrs75.LeafInduction
