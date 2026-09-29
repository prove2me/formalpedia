-- Prove2me | solution 1 for Freiman.lowerHistory_rekey_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:02.193094+00:00
-- url     : https://prove2.me/submissions/16745204-fc1e-4174-876a-5eb6f7d44cea

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

private theorem aq_structural_row (p : LowerHistoryPath) (hp : lowerHistoryStructural p) :
    p.row = match p.catalog with
      | .left => 1
      | .right => 2
      | .mixed => 3
      | .rightMixed => 4
      | .initial => if p.finalParity.1 = p.finalParity.2 then
          if p.finalWider then 1 else 2 else if p.finalWider then 3 else 4 := by
  have hr := hp.2.2.2.2
  cases hc : p.catalog <;>
    simp only [hc, reduceCtorEq, if_true, if_false, false_and, true_and,
      false_or, or_false] at hr ⊢ <;>
    first | exact hr | exact hr.1

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (base : LowerPair) (p p2 : LowerHistoryPath)
    (hp : lowerHistoryStructural p) (hp2 : lowerHistoryStructural p2)
    (hk : lowerHistoryPathKey p2 = lowerHistoryPathKey p) (hr : lowerHistoryReached t h n base p) :
    lowerHistoryReached t h n base p2 ∧ p2.row = p.row := by
  have hfields : p2.catalog = p.catalog ∧ p2.context = p.context ∧
      p2.entry = p.entry ∧ p2.initialWider = p.initialWider ∧ p2.steps = p.steps := by
    simpa only [lowerHistoryPathKey, Prod.mk.injEq] using hk
  obtain ⟨hcatalog, hcontext, hentry, hwider, hsteps⟩ := hfields
  have hfinal : lowerHistoryFinalState p2 = lowerHistoryFinalState p := by
    simp only [lowerHistoryFinalState, lowerHistoryInitialState,
      hcatalog, hcontext, hentry, hwider, hsteps]
  have hparity : p2.finalParity = p.finalParity := by
    calc
      p2.finalParity = (lowerHistoryFinalState p2).context.parity :=
        hp2.2.2.2.1.2.2.1.symm
      _ = (lowerHistoryFinalState p).context.parity :=
        congrArg (fun s : LowerHistoryState => s.context.parity) hfinal
      _ = p.finalParity := hp.2.2.2.1.2.2.1
  have hfinalWider : p2.finalWider = p.finalWider := by
    calc
      p2.finalWider = (lowerHistoryFinalState p2).wider := hp2.2.2.2.1.2.2.2.symm
      _ = (lowerHistoryFinalState p).wider :=
        congrArg (fun s : LowerHistoryState => s.wider) hfinal
      _ = p.finalWider := hp.2.2.2.1.2.2.2
  constructor
  · simpa only [lowerHistoryReached, lowerHistoryRealizes, lowerHistoryReplay,
      hcatalog, hcontext, hentry, hwider, hsteps] using hr
  · rw [aq_structural_row p2 hp2, aq_structural_row p hp,
      hcatalog, hparity, hfinalWider]

#print axioms solution
