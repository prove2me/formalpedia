-- Prove2me | solution 1 for Freiman.other22_residual_capture
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:08:07.779234+00:00
-- url     : https://prove2.me/submissions/8ae4a406-872f-47e7-8cae-6d52fa679c41

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_lowerHistory_complement

open Freiman

theorem solution (p : LowerHistoryPath) (ai bi : ℕ) (bs cs : List CertBound) (g : LowerHistoryComparison)
    (hai : (lowerHistorySourcePremises p)[ai]? = some bs)
    (hbi : (lowerHistoryEndpointComparisons p)[bi]? = some (cs,g))
    (r s q : ℝ) (hs : lowerHistoryConditions bs r s q)
    (hc : lowerHistoryConditions cs r s q) (hn : ¬ lowerHistoryComparisonHolds g r s q) :
    lowerHistoryConditions (lowerHistoryResidual p ai (bi : ℤ)) r s q := by
  classical
  unfold lowerHistoryResidual
  rw [if_neg (by omega),Int.toNat_natCast,hai,hbi]
  dsimp only [Option.getD_some]
  intro b hb
  simp only [List.mem_eraseDups,List.mem_append] at hb
  rcases hb with (hb | hb) | hb
  · exact hs b hb
  · exact hc b hb
  · cases g with
    | automatic => simp at hb
    | impossible => simp at hb
    | bound a =>
      simp only [List.mem_singleton] at hb
      subst b
      exact (lowerHistory_complement a r s q).mpr hn
