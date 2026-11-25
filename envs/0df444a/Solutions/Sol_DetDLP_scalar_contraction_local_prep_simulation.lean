-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_prep_simulation
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:10:31.608837+00:00
-- url     : https://prove2.me/submissions/24cb942f-def0-4751-91dc-a70b7f112df7

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

def haltPrep : BitProgram.Program 8 20 1 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := fun _ => .halt

def emptyGraph : BipartiteMultigraph where
  nV := 0
  nE := 0
  endpoints := fun e => Fin.elim0 e
  side := fun v => Fin.elim0 v
  bipartite := fun e => Fin.elim0 e

lemma trace_zero_eq {α} {step : α → Option α} {a b : α}
    (h : Trace step 0 a b) : a = b := by
  cases h
  rfl

/--
`prep_simulation` asserts an arbitrary prep program meets an arbitrary halted
configuration in `prepSteps` steps. With the halt program and `prepSteps = 0`,
`Trace` forces equality of endpoints, but `initial` has `pc = some entry`
while the target has `pc = none`.
-/
theorem solution :
    ¬ (∀ {s lp : ℕ} (prep : BitProgram.Program 8 (20 + s) lp)
        (context : Fin s → List Bool) (B x y cap0 prepSteps : ℕ) (reg : Fin 8 → Bool)
        (β P ℓ' : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (U : ℕ) (hctx : ∀ i, (context i).length ≤ U) (hB : 0 < B) (hflag : reg 1 = true),
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
        BitProgram.Trace prep prepSteps start ⟨none, reg, pack x y 1 0 0 0⟩ ∧
          (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
            ∀ i, (c.stacks i).length ≤ cap0)) := by
  intro h
  let reg : Fin 8 → Bool := fun i => decide (i.val = 1)
  have hflag : reg 1 = true := by simp [reg]
  have hconj :=
    h (s := 0) (lp := 1) haltPrep (fun i : Fin 0 => i.elim0) 1 0 0 0 0 reg 2 1 1 [] emptyGraph 0
      (fun i => i.elim0) (Nat.succ_pos 0) hflag
  have heq := trace_zero_eq hconj.1
  have hpc := congrArg BitProgram.Cfg.pc heq
  simp [BitProgram.initial, haltPrep] at hpc
