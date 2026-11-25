-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_prep_program
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T20:15:32.444023+00:00
-- url     : https://prove2.me/submissions/8d9e3732-0bed-4482-9e97-17e3a8fc8051
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_scalar_contraction_local_prep_simulation

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

/--
Existence of preparation microprogram parameters reduces to the pointwise
simulation lemma `scalar_contraction_local_prep_simulation` for a fixed program.
-/
theorem solution
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (prep : BitProgram.Program 8 (20 + s) lp),
      ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (context : Fin s → List Bool) (B x y cap0 prepSteps : ℕ) (reg : Fin 8 → Bool) (U : ℕ),
        (∀ i, (context i).length ≤ U) → 0 < B → reg 1 = true →
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s) (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
        BitProgram.Trace prep prepSteps start ⟨none, reg, pack x y 1 0 0 0⟩ ∧
          (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c → ∀ i, (c.stacks i).length ≤ cap0) := by
  refine ⟨0, 1, { inputStack := 0, outputStack := 0, entry := 0, code := ![.halt] }, ?_⟩
  intro β P ℓ' Told desc G context B x y cap0 prepSteps reg U hctx hB hflag
  simpa using
    scalar_contraction_local_prep_simulation (s := 0) (lp := 1)
      { inputStack := 0, outputStack := 0, entry := 0, code := ![.halt] }
      context B x y cap0 prepSteps reg β P ℓ' desc G U hctx hB hflag