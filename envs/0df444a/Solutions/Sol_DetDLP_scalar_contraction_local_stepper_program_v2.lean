-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_stepper_program_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:10:00.358953+00:00
-- url     : https://prove2.me/submissions/722381fe-1d3b-48e0-b17b-c448640b2365

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

lemma trace_zero_eq {α} {step : α → Option α} {a b : α}
    (h : Trace step 0 a b) : a = b := by
  cases h
  rfl

/--
`stepper_program_v2` still universally quantifies `T` (and `F`). Instantiating the
witnessed stepper at `T = 0` with a constantly-`value 0` oracle forces a length-0
trace from a live PC to a halted configuration.
-/
theorem solution :
    ¬ (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se),
          it ≠ iv → ot ≠ ov →
          ∀ (s : ℕ),
            ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
              ∀ (context : Fin s → List Bool) (F : ℕ → ℕ → Answer) (B T U depth x y : ℕ),
                (∀ i, (context i).length ≤ U) → 0 < B →
                let q := B + 1
                let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
                  let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
                  Fin.addCases (m := 20) (n := s)
                    (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits))
                    context
                let small (z : Answer) := match z with
                  | .value v => v < B
                  | .call a b => a < B ∧ b < B
                let returned (a b stack : ℕ) (z : Answer) := match z with
                  | .value v => pack a b stack 0 v 0
                  | .call save child => pack a b stack 1 child save
                ∀ (a b stack : ℕ) (r : Fin 8 → Bool), a < B → b < B →
                  stack < q ^ (depth + 1) → small (F a b) →
                  let start : BitProgram.Cfg 8 (20 + s) lc :=
                    ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
                  ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
                    BitProgram.Trace stepper steps start
                      ⟨none, r', returned a b stack (F a b)⟩ ∧
                    ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                      ∀ i, (c.stacks i).length ≤ U) := by
  intro h
  let Q : BitProgram.Program 3 3 1 :=
    { inputStack := 0, outputStack := 1, entry := 0, code := fun _ => .halt }
  obtain ⟨lc, stepper, hstep⟩ :=
    h 1 1 (by decide) (by decide) (se := 3) (le := 1) Q
      (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide) 0
  let F : ℕ → ℕ → Answer := fun _ _ => .value 0
  have ⟨steps, r', hsteps, htrace, _⟩ :=
    hstep (fun i : Fin 0 => i.elim0) F 1 0 0 0 0 0
      (fun i => i.elim0) (Nat.succ_pos 0)
      0 0 0 (fun _ => false) (Nat.succ_pos 0) (Nat.succ_pos 0)
      (by decide : (0 : ℕ) < (1 + 1) ^ (0 + 1)) (by decide : (0 : ℕ) < 1)
  have h0 : steps = 0 := Nat.eq_zero_of_le_zero hsteps
  subst h0
  have heq := trace_zero_eq htrace
  have hpc := congrArg BitProgram.Cfg.pc heq
  simp [BitProgram.Cfg.pc] at hpc
