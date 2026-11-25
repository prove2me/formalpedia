-- Prove2me | solution 3 for DetDLP.scalar_contraction_local_stepper_program_v3
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:31:01.514814+00:00
-- url     : https://prove2.me/submissions/7a93b142-7c85-4a64-bbae-65df5b4b87a2

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Stack 9 of the packed frame is the constant bit-list `(1 : ℕ).bits`,
independent of the numeric arguments. -/
lemma pack_stack_one {s : ℕ} (context : Fin s → List Bool)
    (q a b stack tag arg save : ℕ) :
    Fin.addCases (m := 20) (n := s)
      (Fin.addCases (m := 8) (n := 12) (fun _ => ([] : List Bool))
        (fun j => (![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0] j).bits))
      context ⟨9, by omega⟩ = (1 : ℕ).bits := by
  have houter : (⟨9, by omega⟩ : Fin (20 + s)) =
      Fin.castAdd s (Fin.natAdd 8 (⟨1, by decide⟩ : Fin 12)) := by
    apply Fin.ext
    simp [Fin.castAdd, Fin.natAdd]
  have hidx : (⟨1, by decide⟩ : Fin 12) = Fin.succ (0 : Fin 11) := by
    apply Fin.ext
    rfl
  rw [houter, Fin.addCases_left, Fin.addCases_right, hidx]
  simp [Matrix.cons_val_succ, Matrix.cons_val_zero, Nat.one_bits]

/--
`stepper_program_v3` demands one stepper whose every trace, including the
initial configuration, keeps all stacks of length at most `U`. Taking
`answer = 0`, `B = 1`, and `U = 0` makes the context empty, while the packed
frame always stores `(1).bits` on stack 9.
-/
theorem solution :
    ¬ (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se),
          it ≠ iv → ot ≠ ov →
          ∀ (s : ℕ) (hs : 0 < s),
            ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
              ∀ (answer B U depth x y : ℕ) (context : Fin s → List Bool),
                0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
                (∀ i, (context i).length ≤ U) →
                let F : ℕ → ℕ → Answer := fun _ _ => .value answer
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
                ∃ T : ℕ,
                  ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
                    a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
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
  have hs1 : 0 < (1 : ℕ) := by decide
  obtain ⟨lc, stepper, hstep⟩ :=
    h 1 1 (by decide) (by decide) (se := 3) (le := 1) Q
      (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)
      1 hs1
  let answer : ℕ := 0
  let B : ℕ := 1
  let U : ℕ := 0
  let context : Fin 1 → List Bool := fun _ => []
  have hctx : context ⟨0, hs1⟩ = answer.bits := by
    simp [context, answer, Nat.zero_bits]
  have hU : ∀ i, (context i).length ≤ U := by
    intro i
    simp [context, U]
  obtain ⟨T, hT⟩ :=
    hstep answer B U 0 0 0 context (by decide) (by decide) hctx hU
  let r : Fin 8 → Bool := fun _ => false
  obtain ⟨steps, r', _hle, _htr, hcap⟩ :=
    hT 0 0 0 r (by decide) (by decide) (by decide) (by decide)
  let start : BitProgram.Cfg 8 (20 + 1) lc :=
    ⟨some stepper.entry, r, let q := B + 1
      let v : Fin 12 → ℕ := ![q, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      Fin.addCases (m := 20) (n := 1)
        (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context⟩
  have hlen := hcap 0 start (Nat.zero_le _) (Trace.refl start)
  have h9 := hlen ⟨9, by omega⟩
  have hone : start.stacks ⟨9, by omega⟩ = (1 : ℕ).bits := by
    simpa [start, context, B] using
      (pack_stack_one (s := 1) context (B + 1) 0 0 0 0 0 0)
  rw [hone] at h9
  simp [Nat.one_bits] at h9
  omega
