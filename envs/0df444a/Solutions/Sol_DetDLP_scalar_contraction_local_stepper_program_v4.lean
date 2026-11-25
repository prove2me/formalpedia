-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_stepper_program_v4
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T05:00:33.40106+00:00
-- url     : https://prove2.me/submissions/2b497de5-5b01-44f9-bd43-f72f278fd877

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_scalar_contraction_local_stepper_copy_v4

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/-- Drop the concrete `T`/`U` length bounds from `stepper_copy_v4`. -/
theorem solution (s : ℕ) (hs : 0 < s) :
    ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (answer B depth : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
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
        ∃ (T U : ℕ),
          (∀ i, (context i).length ≤ U) ∧
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U := by
  obtain ⟨lc, stepper, hcopy⟩ := scalar_contraction_local_stepper_copy_v4 s hs
  refine ⟨lc, stepper, ?_⟩
  intro answer B depth context hB ha hctx
  obtain ⟨T, U, hU, _hT, _hUbound, hrun⟩ := hcopy answer B depth context hB ha hctx
  exact ⟨T, U, hU, hrun⟩
