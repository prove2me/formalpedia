-- Prove2me | solution 1 for DeletionCode.Recovery.State.score_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:17.794426+00:00
-- url     : https://prove2.me/submissions/a7673520-f813-483c-a308-fc87b66f8eba

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
variable [Fintype B]
open DeletionCode.Recovery.State
namespace DeletionCode.Recovery.State
theorem _root_.solution (s : State B) (b : B) (w : Slot)
    (hb : ¬ s.Started b) : (s.start b w).score = s.score + 1 := by
  classical
  have heq : (s.start b w).startedSet = insert b s.startedSet := by
    apply Finset.ext
    intro a
    change (a ∈ Finset.univ.filter
      (fun x => Function.update s.seed b (some w) x ≠ none)) ↔
      a ∈ insert b (Finset.univ.filter (fun x => s.seed x ≠ none))
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hab : a = b
    · subst a
      simp
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba]
  have hnot : b ∉ s.startedSet := by
    simpa [startedSet, Started] using hb
  change (s.start b w).startedSet.card + s.filled.card = s.score + 1
  rw [heq, Finset.card_insert_of_notMem hnot]
  unfold score
  omega
end DeletionCode.Recovery.State
