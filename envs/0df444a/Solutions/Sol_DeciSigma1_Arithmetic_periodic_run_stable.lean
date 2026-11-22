-- Prove2me | solution 1 for DeciSigma1.Arithmetic.periodic_run_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:25.853808+00:00
-- url     : https://prove2.me/submissions/a4b1b16c-9182-4158-b3ac-57feed638122

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_card_add_factorial
public import Theorems.Thm_DeciSigma1_Arithmetic_streamPeriod_mul
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_add
public import Theorems.Thm_DeciSigma1_runFrom_append
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
theorem _root_.solution [Fintype S] (T : Table α S k) (q : S) (ξ : ℕ → α) {d p : ℕ}
    (hξ : StreamPeriod ξ d) (hp : Fintype.card S * d ≤ p) (m : ℕ) :
    runFrom T.step q (streamPrefix ξ (p + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (streamPrefix ξ p) := by
  set N := Fintype.card S
  set r := p - N * d
  let F : S → S := fun s => runFrom T.step s (streamPrefix (fun i => ξ (r + i)) d)
  have hblock : ∀ j, runFrom T.step q (streamPrefix ξ (r + j * d)) =
      F^[j] (runFrom T.step q (streamPrefix ξ r)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show r + (j + 1) * d = (r + j * d) + d by ring, streamPrefix_add,
        runFrom_append, ih, Function.iterate_succ_apply']
      congr 2
      funext i
      rw [show r + j * d + i = (r + i) + j * d by ring, streamPeriod_mul hξ]
  have h1 : p = r + N * d := by omega
  have h2 : p + m * (d * N.factorial) = r + (N + m * N.factorial) * d := by rw [h1]; ring
  rw [h2, hblock, h1, hblock]
  exact iterate_card_add_factorial F _ m
end DeciSigma1.Arithmetic
