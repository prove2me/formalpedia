-- Prove2me | solution 1 for DeciSigma1.Words.streamPeriod_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:43.974433+00:00
-- url     : https://prove2.me/submissions/18c8bd29-d453-4529-b46a-17c83fd0583a

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution {ξ : ℕ → α} {p q : ℕ}
    (hp : StreamPeriod ξ p) (hq : StreamPeriod ξ q) : StreamPeriod ξ (Nat.gcd p q) := by
  intro i
  let n := i + p + q + Nat.gcd p q + 1
  have hg := (streamPeriod_prefix hp n).gcd (streamPeriod_prefix hq n) (by simp [n]; omega)
  have hh := (List.hasPeriod_iff_getElem?.mp hg) i (by simp [n]; omega)
  have hi : i < n := by dsimp [n]; omega
  have hj : i + Nat.gcd p q < n := by dsimp [n]; omega
  simpa only [streamPrefix, List.getElem?_ofFn, dif_pos hi, dif_pos hj,
    Option.some.injEq] using hh.symm
end DeciSigma1.Words
