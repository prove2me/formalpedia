-- Prove2me | solution 1 for DeciSigma1.Words.leastPeriod_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:10.395949+00:00
-- url     : https://prove2.me/submissions/60afb3f6-a633-4968-b462-bb41873453b0

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_streamPeriod_gcd

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution {ξ : ℕ → α} {p q : ℕ} (hp : LeastStreamPeriod ξ p) :
    StreamPeriod ξ q ↔ p ∣ q := by
  constructor
  · intro hper
    have hg := streamPeriod_gcd hp.2.1 hper
    have hgp := Nat.gcd_pos_of_pos_left q hp.1
    have hmin := hp.2.2 (Nat.gcd p q) hgp hg
    have hle := Nat.gcd_le_left q hp.1
    have he : Nat.gcd p q = p := by omega
    rw [← he]; exact Nat.gcd_dvd_right p q
  · intro hd i
    rw [streamPeriod_mod hp.2.1 (i + q), streamPeriod_mod hp.2.1 i]
    congr 1
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
end DeciSigma1.Words
