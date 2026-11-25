-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_prep_program_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T00:16:14.525144+00:00
-- url     : https://prove2.me/submissions/903385f2-c159-4a7a-bba8-57fab5965e86

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

def emptyGraph : BipartiteMultigraph where
  nV := 0
  nE := 0
  endpoints := fun e => Fin.elim0 e
  side := fun v => Fin.elim0 v
  bipartite := fun e => Fin.elim0 e

private lemma bits_two_length : ((2 : ℕ).bits).length = 2 := by
  decide

/--
`prep_program_v2` still universally quantifies `cap0`. With `B = 1` and `cap0 = 0`,
the packed halt configuration places `q.bits` (`q = 2`) on stack index 8, so the
final stack-length bound `≤ 0` fails.
-/
theorem solution :
    ¬ (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se),
          it ≠ iv → ot ≠ ov →
          ∃ (s lp : ℕ) (prep : BitProgram.Program 8 (20 + s) lp),
            ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
              (context : Fin s → List Bool) (B x y cap0 : ℕ) (reg : Fin 8 → Bool)
              (U : ℕ),
              (∀ i, (context i).length ≤ U) → 0 < B → reg 1 = true →
              let q := B + 1
              let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
                let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
                Fin.addCases (m := 20) (n := s)
                  (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits))
                  context
              let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
              ∃ prepSteps : ℕ,
                BitProgram.Trace prep prepSteps start ⟨none, reg, pack x y 1 0 0 0⟩ ∧
                  (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
                    ∀ i, (c.stacks i).length ≤ cap0)) := by
  intro h
  let Q : BitProgram.Program 3 3 1 :=
    { inputStack := 0, outputStack := 1, entry := 0, code := fun _ => .halt }
  obtain ⟨s, lp, prep, hprep⟩ :=
    h 1 1 (by decide) (by decide) (se := 3) (le := 1) Q
      (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)
  let reg : Fin 8 → Bool := fun i => decide (i.val = 1)
  have hflag : reg 1 = true := by simp [reg]
  let context : Fin s → List Bool := fun _ => []
  obtain ⟨prepSteps, htrace, hcap⟩ :=
    hprep 2 1 1 1 [] emptyGraph context 1 0 0 0 reg 0
      (fun _ => Nat.zero_le _) (by decide) hflag
  have hbound := hcap prepSteps _ le_rfl htrace
  have h8 := hbound ⟨8, by omega⟩
  have heq8 :
      (let q := (1 : ℕ) + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits))
            context
        pack 0 0 1 0 0 0 ⟨8, by omega⟩) = (2 : ℕ).bits := by
    simp [Fin.addCases]
  have : ((2 : ℕ).bits).length ≤ 0 := by
    simpa [heq8] using h8
  have hpos : 0 < ((2 : ℕ).bits).length := by
    simpa [bits_two_length] using (Nat.succ_pos 1)
  exact (not_lt_of_ge this) hpos
