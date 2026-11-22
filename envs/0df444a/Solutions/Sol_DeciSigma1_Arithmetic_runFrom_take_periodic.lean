-- Prove2me | solution 1 for DeciSigma1.Arithmetic.runFrom_take_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:13.220211+00:00
-- url     : https://prove2.me/submissions/53684a69-4062-4a83-b56e-50776eca918a

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Theorems.Thm_DeciSigma1_Arithmetic_periodic_run_stable
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_eq_of_mod
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Arithmetic
theorem _root_.solution [Fintype S] (T : Table α S k) (q : S) {u : List α} {d o : ℕ}
    (hd : 0 < d) (hper : Words.PeriodicOn u d 0 u.length) (ho : Fintype.card S * d ≤ o) (m : ℕ)
    (hlen : o + m * (d * (Fintype.card S).factorial) ≤ u.length) :
    runFrom T.step q (u.take (o + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (u.take o) := by
  have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨q⟩
  have hdu : d ≤ u.length := by
    have : d ≤ Fintype.card S * d := Nat.le_mul_of_pos_left d hN
    omega
  let ξ : ℕ → α := fun i => u[i % d]'(by have := Nat.mod_lt i hd; omega)
  have hξ : StreamPeriod ξ d := by intro i; simp [ξ]
  have htake : ∀ n ≤ u.length, streamPrefix ξ n = u.take n := by
    intro n hn
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [streamPrefix, List.getElem_ofFn, List.getElem_take, ξ]
    have hi : i < u.length := by simp at h1; omega
    have := hper.eq_of_mod (p := i % d) (q := i) (Nat.zero_le _) (Nat.zero_le _)
      (by have := Nat.mod_lt i hd; omega) hi (Nat.mod_mod i d)
    rw [List.getElem?_eq_getElem (by have := Nat.mod_lt i hd; omega),
      List.getElem?_eq_getElem hi] at this
    exact Option.some.inj this
  rw [← htake _ hlen, ← htake _ (by omega)]
  exact periodic_run_stable T q ξ hξ ho m
end DeciSigma1.Arithmetic
