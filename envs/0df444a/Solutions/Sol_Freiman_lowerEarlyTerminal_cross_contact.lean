-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_cross_contact
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:14:13.454722+00:00
-- url     : https://prove2.me/submissions/649ca302-4dc6-4930-a011-f1766bf61201

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

theorem solution (p : LowerPair) (a b : LowerLabel)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (h1 : lowerEarlyTerminalKindHolds p (.compare (section14LabelWords a) true (section14LabelWords b) false false))
    (h2 : lowerEarlyTerminalKindHolds p (.compare (section14LabelWords b) true (section14LabelWords a) false false)) :
    lowerEarlyTerminalContact p a b := by
  have happ : ∀ l : LowerLabel,
      lowerHistoryAppend (lowerNormalize p) (section14LabelWords l) = lowerChild p l := fun _ => rfl
  simp only [lowerEarlyTerminalKindHolds, lowerEarlyTerminalEndpoint, lowerHistoryEndpointReal,
    Bool.false_eq_true, if_false, happ] at h1 h2
  have key : lowerEndpoint (lowerChild p b) false ≤ lowerEndpoint (lowerChild p a) true ∧
      lowerEndpoint (lowerChild p a) false ≤ lowerEndpoint (lowerChild p b) true := by
    cases hoo : lowerHistoryCommonOdd (lowerNormalize p) ⟨([],[]),(false,false)⟩ with
    | false =>
      rw [hoo] at h1 h2
      norm_num at h1 h2
      exact ⟨h1, h2⟩
    | true =>
      rw [hoo] at h1 h2
      norm_num at h1 h2
      exact ⟨h2, h1⟩
  obtain ⟨hab, hba⟩ := key
  unfold lowerEarlyTerminalContact lowerCover
  refine ⟨max (lowerEndpoint (lowerChild p a) false) (lowerEndpoint (lowerChild p b) false), ?_, ?_⟩
  · exact Set.mem_Icc.mpr ⟨le_max_left _ _, max_le (ho _) hab⟩
  · exact Set.mem_Icc.mpr ⟨le_max_right _ _, max_le hba (ho _)⟩
