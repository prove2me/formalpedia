-- Prove2me | solution 1 for DeciSigma1.Words.leastPeriod_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:19.020898+00:00
-- url     : https://prove2.me/submissions/a59517b9-5a72-4be9-8828-739041b6fe3b

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Theorems.Thm_DeciSigma1_Words_leastPeriod_pos
public import Theorems.Thm_DeciSigma1_Words_hasPeriod_leastPeriod
public import Theorems.Thm_DeciSigma1_Words_leastPeriod_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
variable [DecidableEq α] {w : List α} {p g : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (h : w.HasPeriod g) (h2 : 2 * g ≤ w.length) : leastPeriod w ∣ g := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact dvd_zero _
  have hle : leastPeriod w ≤ g := leastPeriod_le hg h
  have hpos := leastPeriod_pos w
  have hgcd := (hasPeriod_leastPeriod w).gcd h (by
    have := Nat.gcd_pos_of_pos_left g hpos
    omega)
  have h1 : leastPeriod w ≤ (leastPeriod w).gcd g :=
    leastPeriod_le (Nat.gcd_pos_of_pos_left g hpos) hgcd
  have h2 : (leastPeriod w).gcd g ≤ leastPeriod w := Nat.gcd_le_left g hpos
  have heq : (leastPeriod w).gcd g = leastPeriod w := le_antisymm h2 h1
  rw [← heq]
  exact Nat.gcd_dvd_right _ _
end DeciSigma1.Words
