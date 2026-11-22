-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.window_rotate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:38.803886+00:00
-- url     : https://prove2.me/submissions/cfadb7c3-8fe4-4f5e-a39d-91ab482698e5

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}
namespace DeciSigma1.Words.PeriodicOn
theorem _root_.solution (h : PeriodicOn w d s e) (he : e ≤ w.length) {z : ℕ} (hsz : s ≤ z)
    (hz : z + d ≤ e) : (w.drop z).take d = ((w.drop s).take d).rotate ((z - s) % d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  apply List.ext_getElem?
  intro i
  by_cases hi : i < d
  · have hlen : ((w.drop s).take d).length = d := by simp; omega
    rw [List.getElem?_rotate (by omega), hlen, List.getElem?_take_of_lt hi, List.getElem?_drop,
      List.getElem?_take_of_lt (Nat.mod_lt _ hd), List.getElem?_drop]
    apply h.eq_of_mod (by omega) (by omega) (by omega)
      (by have := Nat.mod_lt (i + (z - s) % d) hd; omega)
    have h1 : (i + (z - s) % d) % d ≡ i + (z - s) [MOD d] :=
      (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ (Nat.mod_modEq _ _))
    have h2 := Nat.ModEq.add_left s h1
    rw [show s + (i + (z - s)) = z + i by omega] at h2
    exact h2.symm
  · have h1 : ((w.drop z).take d).length ≤ i := by simp only [List.length_take]; omega
    have h2 : (((w.drop s).take d).rotate ((z - s) % d)).length ≤ i := by
      simp only [List.length_rotate, List.length_take]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]
end DeciSigma1.Words.PeriodicOn
