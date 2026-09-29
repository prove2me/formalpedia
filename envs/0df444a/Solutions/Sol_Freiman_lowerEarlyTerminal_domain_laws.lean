-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_domain_laws
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:38:48.798873+00:00
-- url     : https://prove2.me/submissions/46907125-c336-4b59-9ef2-3404ae176633

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution (hc : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∃ i : Fin 3, lowerEnds (lowerNormalize p).1 (lowerEarlyTerminalShortCatalog i).leftContext)
    (hf : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∀ C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3],
        lowerEnds (lowerNormalize p).1 C.leftContext → lowerEarlyTerminalMatches p C)
    (hr : ∀ t p, lowerState t p → lowerEarlyDomain p →
      ∀ C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3],
        lowerEnds (lowerNormalize p).1 C.leftContext →
          certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p)) :
    LowerEarlyTerminalDomainLaws := by
  intro t p hs hd
  have hshort : ∀ i : Fin 3, lowerEarlyTerminalShortCatalog i ∈
      [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3] := by
    intro i
    fin_cases i <;> simp [lowerEarlyTerminalShortCatalog, lowerEarlyTerminalCatalog]
  have hterm : ∀ i : Fin 3, lowerEarlyTerminalTerminalCatalog i ∈
      [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3] := by
    intro i
    fin_cases i <;> simp [lowerEarlyTerminalTerminalCatalog, lowerEarlyTerminalCatalog]
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi⟩ := hc t p hs hd
    exact ⟨i, hf t p hs hd _ (hshort i) hi, hr t p hs hd _ (hshort i) hi⟩
  · intro i hi
    exact ⟨hf t p hs hd _ (hterm i) hi, hr t p hs hd _ (hterm i) hi⟩
