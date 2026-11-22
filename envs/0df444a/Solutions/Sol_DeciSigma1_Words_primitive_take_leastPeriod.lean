-- Prove2me | solution 1 for DeciSigma1.Words.primitive_take_leastPeriod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:22.407809+00:00
-- url     : https://prove2.me/submissions/6ce2b621-500c-4d2e-a0ae-71294af32de3

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
namespace DeciSigma1.Words
theorem _root_.solution [DecidableEq α] {w : List α}
    (h2 : 2 * leastPeriod w ≤ w.length) : IsPrimitive (w.take (leastPeriod w)) := by
  set p := leastPeriod w with hp_def
  have hpos : 0 < p := leastPeriod_pos w
  have hlen : (w.take p).length = p := by simp; omega
  rw [isPrimitive_iff_period]
  refine
      ⟨by intro h; rw [← List.length_eq_zero_iff, hlen] at h; omega, fun q hq hqp hdvd hper => ?_⟩
  rw [hlen] at hqp hdvd
  -- `w` would have the smaller period `q`
  have hw : w.HasPeriod q := by
    rw [List.hasPeriod_iff_forall_getElem?_mod]
    intro i hi
    have hwp := hasPeriod_leastPeriod w
    rw [List.hasPeriod_iff_forall_getElem?_mod] at hwp hper
    rw [hlen] at hper
    rw [hwp i hi, ← List.getElem?_take_of_lt (Nat.mod_lt i hpos),
      hper _ (Nat.mod_lt i hpos), List.getElem?_take_of_lt (lt_trans (Nat.mod_lt _ hq) hqp),
      Nat.mod_mod_of_dvd _ hdvd]
  exact absurd (leastPeriod_le hq hw) (by omega)
end DeciSigma1.Words
