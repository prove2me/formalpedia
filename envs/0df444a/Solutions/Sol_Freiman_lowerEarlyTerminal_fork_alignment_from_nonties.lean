-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_fork_alignment_from_nonties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:20:33.931109+00:00
-- url     : https://prove2.me/submissions/ab8e0ace-8dfc-4506-a316-9bd816fa0140

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

private theorem norm_keep (X : LowerPair) (h : lowerWidth X.2 ≤ lowerWidth X.1) :
    lowerNormalize X = X := by unfold lowerNormalize; simp [h]

private theorem norm_swap (X : LowerPair) (h : ¬ lowerWidth X.2 ≤ lowerWidth X.1) :
    lowerNormalize X = (X.2, X.1) := by unfold lowerNormalize; simp [h]

theorem solution (p : LowerPair) (l : LowerLabel) (hw : LowerHistoryWidthLaw)
    (hswap : ∀ w : LowerPair, LowerEarlyTerminalNoTies w → ∀ upper : Bool,
      lowerEndpoint w upper = lowerEndpoint (w.2,w.1) upper)
    (hn : ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d)) :
    lowerEarlyTerminalForkAlignment p l := by
  intro wide norm hm hat d hd upper
  have hwl := (hw (lowerNormalize p) (section14LabelWords l)).1
  simp only [section14NormalCases, List.mem_cons, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hm
  · have hle : lowerWidth ((lowerNormalize p).2 ++ l.2)
        ≤ lowerWidth ((lowerNormalize p).1 ++ l.1.reverse) := hwl.mpr hat
    have hnorm := norm_keep ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) hle
    simp only [lowerChild, lowerEarlyTerminalForkPair, lowerEarlyTerminalForkWords,
      lowerHistoryAppend, lowerHistorySet, lowerHistoryPick, section14LabelWords, hnorm,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
      List.append_assoc, Bool.false_eq_true, if_false]
  · have hb : certBoundHolds ⟨true,true,lowerHistoryWH (section14LabelWords l)⟩
        (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p) := by
      have h0 := hat
      unfold lowerEarlyTerminalAt section14Holds at h0
      exact h0 _ (by simp)
    have hnot : ¬ lowerHistoryAtBase (lowerNormalize p)
        [⟨false,false,lowerHistoryWH (section14LabelWords l)⟩] := by
      intro hcc
      have h2 := hcc ⟨false,false,lowerHistoryWH (section14LabelWords l)⟩ (by simp)
      simp only [certBoundHolds, if_true, Bool.false_eq_true, if_false] at hb h2
      unfold lowerEarlyTerminalR lowerEarlyTerminalS lowerEarlyTerminalQ at hb
      linarith
    have hlt : ¬ (lowerWidth ((lowerNormalize p).2 ++ l.2)
        ≤ lowerWidth ((lowerNormalize p).1 ++ l.1.reverse)) := fun hcon => hnot (hwl.mp hcon)
    have hnorm := norm_swap ((lowerNormalize p).1 ++ l.1.reverse, (lowerNormalize p).2 ++ l.2) hlt
    rw [hswap (lowerEarlyTerminalForkPair p l true d) (hn d hd) upper]
    simp only [lowerChild, lowerEarlyTerminalForkPair, lowerEarlyTerminalForkWords,
      lowerHistoryAppend, lowerHistorySet, lowerHistoryPick, section14LabelWords, hnorm,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_nil,
      List.append_assoc, if_true]
  · exact absurd hm (by simp)
