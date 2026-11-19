-- Prove2me | solution 1 for DeletionCode.Recovery.terminal_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:52:21.787986+00:00
-- url     : https://prove2.me/submissions/3f2e216f-815e-42bc-9467-031ff368f9cf

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Recovery
import Theorems.Thm_DeletionCode_Recovery_terminal_started_complete

set_option autoImplicit true
open DeletionCode DeletionCode.Recovery
variable {B : Type*} [DecidableEq B]
open State
namespace DeletionCode.Recovery
theorem _root_.solution (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hstop : ∀ s', ¬ Step M s s') :
    ∀ b, s.Complete b := by
  classical
  have hstarted := terminal_started_complete M s hstop
  have along : ∀ {a b}, Reach M.adjacent a b →
      s.Complete a → s.Complete b := by
    intro a b hpath
    induction hpath with
    | refl => exact fun h => h
    | @tail b c hpath hadj ih =>
      intro ha
      have hb : s.Complete b := ih ha
      by_cases hc : s.Started c
      · exact hstarted c hc
      · exact False.elim (hstop _ (Step.startAdjacent s b c 0 hb hadj hc))
  intro b
  obtain ⟨r, hr, hpath⟩ := M.rooted b
  exact along hpath (hs.2 r hr)
end DeletionCode.Recovery
