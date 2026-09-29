-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_coverage_sound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:12:13.173251+00:00
-- url     : https://prove2.me/submissions/ae39a532-c9a1-46d3-b3c4-f1d84cbb962e

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

private theorem not_complement {h : CertBound} {r s q : ℝ}
    (hn : ¬ certBoundHolds (lowerHistoryComplement h) r s q) : certBoundHolds h r s q := by
  cases h with
  | mk lower strict threshold =>
    simp only [certBoundHolds, lowerHistoryComplement] at hn ⊢
    cases lower <;> cases strict <;> simp_all [not_lt, not_le]

theorem solution (C : LowerEarlyTerminalCatalog) (hc : lowerEarlyTerminalCoverage C)
    (hr : lowerEarlyTerminalRecordsSound C) : lowerEarlyTerminalGoalsSound C := by
  intro r s q hmem g hg hprem b hb hbranch
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hg
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
  have hilen : i < C.goals.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, -⟩; exact h
  have hjlen : j < (lowerEarlyTerminalBranches C g.kind).length := by
    rcases List.getElem?_eq_some_iff.mp hj with ⟨h, -⟩; exact h
  have hgi : lowerEarlyTerminalGoal C i = g := by
    simp only [lowerEarlyTerminalGoal, hi, Option.getD_some]
  have hcov := hc i (List.mem_range.mpr hilen) j
    (List.mem_range.mpr (by rw [hgi]; exact hjlen))
  rw [hgi, hj, Option.getD_some] at hcov
  rcases hcov with hauto | ⟨rec, hrecmem, hrg, hrb⟩
  · rw [hauto]; trivial
  · have hrs := hr rec hrecmem r s q hmem
    rw [hrg, hgi, hrb] at hrs
    simp only [lowerEarlyTerminalResidual, hj, Option.getD_some] at hrs
    have hT : ¬ section14Holds
        (match b.2 with | .bound h => [lowerHistoryComplement h] | _ => []) r s q := by
      intro hTh
      refine hrs ?_
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hprem x hx
      · exact hbranch x hx
      · exact hTh x hx
    simp only [section14ComparisonHolds]
    rcases hb2 : b.2 with _ | _ | h
    · trivial
    · rw [hb2] at hT
      exact absurd (by intro x hx; simp at hx) hT
    · rw [hb2] at hT
      refine not_complement ?_
      intro hch
      exact hT (by intro x hx; simp only [List.mem_singleton] at hx; rw [hx]; exact hch)
