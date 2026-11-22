-- Prove2me | solution 1 for DeciSigma1.Words.period_extend_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:06.955382+00:00
-- url     : https://prove2.me/submissions/beb0b853-322a-42cd-a832-ee97feaa2d3c

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Theorems.Thm_DeciSigma1_Words_periodicOn_iff_hasPeriod

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution {w : List α} {p q s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length)
    (hp : PeriodicOn w p s e) (hq : PeriodicOn w q s e) (hlen : p + q - p.gcd q ≤ e - s) :
    PeriodicOn w (p.gcd q) s e := by
  rw [periodicOn_iff_hasPeriod hse he] at hp hq ⊢
  have hl : ((w.drop s).take (e - s)).length = e - s := by simp; omega
  exact hp.gcd hq (by rw [hl]; exact hlen)
end DeciSigma1.Words
