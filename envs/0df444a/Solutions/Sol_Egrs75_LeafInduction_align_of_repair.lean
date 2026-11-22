-- Prove2me | solution 1 for Egrs75.LeafInduction.align_of_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:20.958162+00:00
-- url     : https://prove2.me/submissions/203c6749-ee0d-4d29-b92b-1745b340f5cd

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75
namespace Egrs75.LeafInduction
theorem _root_.solution {p q : ℕ} (N : ℕ)
    (hrepair : ∀ {n : ℕ}, LowDigits p n → 0 < badCountQ q n →
      ∃ n', n < n' ∧ LowDigits p n' ∧ badCountQ q n' < badCountQ q n)
    (seed : ℕ) (hseedN : N < seed) (hseedp : LowDigits p seed) :
    ∃ n, N < n ∧ LowDigits p n ∧ LowDigits q n := by
  -- Strong induction on the base-`q` potential of the running number, carrying the
  -- invariants `N < n` and `LowDigits p n`.  Generalise over the running number.
  suffices H : ∀ k, ∀ n, badCountQ q n = k → N < n → LowDigits p n →
      ∃ m, N < m ∧ LowDigits p m ∧ LowDigits q m by
    exact H (badCountQ q seed) seed rfl hseedN hseedp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hN hpn
    rcases Nat.eq_zero_or_pos (badCountQ q n) with hzero | hpos
    · -- potential 0 ⟹ already LowDigits q : done with `n` itself
      exact ⟨n, hN, hpn, (badCountQ_eq_zero_iff_lowDigits).mp hzero⟩
    · -- potential > 0 ⟹ repair once, recurse on the strictly smaller potential
      obtain ⟨n', hlt, hpn', hdrop⟩ := hrepair hpn hpos
      -- the new potential `badCountQ q n'` is `< k`
      have hk' : badCountQ q n' < k := by rw [← hk]; exact hdrop
      exact ih (badCountQ q n') hk' n' rfl (lt_trans hN hlt) hpn'
end Egrs75.LeafInduction
