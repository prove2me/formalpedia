-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:21:43.212847+00:00
-- url     : https://prove2.me/submissions/ff844961-203b-48c1-b449-23f3841068ef

import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_000_100
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_100_200
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_200_300
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_300_400
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_400_500
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_500_600
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_600_700
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_pairs_700_752
import Definitions.Def_Freiman_lowerEarlyTerminalDataState2
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ p ∈ lowerEarlyTerminalState2.pairs, lowerEarlyTerminalPairValid lowerEarlyTerminalState2 p := by
  have he : lowerEarlyTerminalState2.pairs = (lowerEarlyTerminalState2.pairs.drop 0).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 100).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 200).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 300).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 400).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 500).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 600).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 700).take 52 := by rfl
  have hc : ∀ p ∈ ((lowerEarlyTerminalState2.pairs.drop 0).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 100).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 200).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 300).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 400).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 500).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 600).take 100 ++ (lowerEarlyTerminalState2.pairs.drop 700).take 52), lowerEarlyTerminalPairValid lowerEarlyTerminalState2 p :=
    List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_state2_pairs_000_100, Freiman.lowerEarlyTerminal_state2_pairs_100_200⟩, Freiman.lowerEarlyTerminal_state2_pairs_200_300⟩, Freiman.lowerEarlyTerminal_state2_pairs_300_400⟩, Freiman.lowerEarlyTerminal_state2_pairs_400_500⟩, Freiman.lowerEarlyTerminal_state2_pairs_500_600⟩, Freiman.lowerEarlyTerminal_state2_pairs_600_700⟩, Freiman.lowerEarlyTerminal_state2_pairs_700_752⟩
  exact Eq.mpr (congrArg (fun ps : List LowerEarlyTerminalPair => ∀ p ∈ ps, lowerEarlyTerminalPairValid lowerEarlyTerminalState2 p) he) hc

#print axioms solution
