-- Prove2me | solution 1 for DeciSigma1.Arithmetic.iterate_card_add_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:37.269712+00:00
-- url     : https://prove2.me/submissions/ef197f17-4cd2-4a36-98b1-23f359e1da23

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
theorem _root_.solution {β : Type} [Fintype β] (f : β → β) (x : β) (m : ℕ) :
    f^[Fintype.card β + m * (Fintype.card β).factorial] x = f^[Fintype.card β] x := by
  set n := Fintype.card β
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => f^[i] x) (by simp [n])
  -- order the two indices
  obtain ⟨a, c, ha, hc, hcn, hac⟩ : ∃ a c : ℕ, a ≤ n ∧ 0 < c ∧ c ≤ n ∧
      f^[a + c] x = f^[a] x := by
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · refine ⟨i, j - i, by omega, by omega, by omega, ?_⟩
      rw [show (i : ℕ) + (j - i) = j by omega]; exact heq.symm
    · refine ⟨j, i - j, by omega, by omega, by omega, ?_⟩
      rw [show (j : ℕ) + (i - j) = i by omega]; exact heq
  have hstep : ∀ t, a ≤ t → f^[t + c] x = f^[t] x := by
    intro t ht
    have := congrArg (f^[t - a]) hac
    rwa [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      show t - a + (a + c) = t + c by omega, show t - a + a = t by omega] at this
  have hrep : ∀ q t, a ≤ t → f^[t + q * c] x = f^[t] x := by
    intro q
    induction q with
    | zero => intro t _; simp
    | succ q ih =>
      intro t ht
      rw [show t + (q + 1) * c = (t + q * c) + c by ring, hstep _ (by omega), ih t ht]
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hc hcn
  rw [hq, show m * (c * q) = (m * q) * c by ring]
  exact hrep _ _ ha
end DeciSigma1.Arithmetic
