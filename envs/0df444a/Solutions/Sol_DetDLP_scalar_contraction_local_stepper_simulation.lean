-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_stepper_simulation
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:10:29.492464+00:00
-- url     : https://prove2.me/submissions/ffa3bb1c-0e3f-4a2b-800a-035177177a3c

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

def haltStepper : BitProgram.Program 8 20 1 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := fun _ => .halt

def Fval (_a _b : ℕ) : Answer := .value 0

lemma trace_zero_eq {α} {step : α → Option α} {a b : α}
    (h : Trace step 0 a b) : a = b := by
  cases h
  rfl

/--
`stepper_simulation` claims an arbitrary stepper simulates an arbitrary oracle `F`
in at most `T` steps. Taking the halt program with `T = 0` and `F ≡ value 0`
forces a length-0 trace from a live PC to a halted configuration.
-/
theorem solution :
    ¬ (∀ {s lc : ℕ} (stepper : BitProgram.Program 8 (20 + s) lc)
        (context : Fin s → List Bool) (F : ℕ → ℕ → Answer) (B T U depth : ℕ)
        (hctx : ∀ i, (context i).length ≤ U) (hB : 0 < B),
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let small (z : Answer) := match z with
          | .value v => v < B
          | .call a b => a < B ∧ b < B
        let returned (a b stack : ℕ) (z : Answer) := match z with
          | .value v => pack a b stack 0 v 0
          | .call save child => pack a b stack 1 child save
        ∀ (a b stack : ℕ) (r : Fin 8 → Bool), a < B → b < B → stack < q ^ (depth + 1) →
          small (F a b) →
          let start : BitProgram.Cfg 8 (20 + s) lc :=
            ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
          ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
            BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
            ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
              ∀ i, (c.stacks i).length ≤ U) := by
  intro h
  have hsim :=
    h (s := 0) (lc := 1) haltStepper (fun i : Fin 0 => i.elim0) Fval 1 0 0 0
      (fun i => i.elim0) (Nat.succ_pos 0)
  have ⟨steps, r', hsteps, htrace, _⟩ :=
    hsim 0 0 0 (fun _ => false) (Nat.succ_pos 0) (Nat.succ_pos 0)
      (by decide : (0 : ℕ) < (1 + 1) ^ (0 + 1)) (by decide : (0 : ℕ) < 1)
  have h0 : steps = 0 := Nat.eq_zero_of_le_zero hsteps
  subst h0
  have heq := trace_zero_eq htrace
  have hpc := congrArg BitProgram.Cfg.pc heq
  simp [haltStepper] at hpc
