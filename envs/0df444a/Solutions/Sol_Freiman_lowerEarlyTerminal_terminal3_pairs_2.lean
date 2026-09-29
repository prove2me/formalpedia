-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_terminal3_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:21:52.643461+00:00
-- url     : https://prove2.me/submissions/f4fe2f9a-f2b3-43e2-8a32-218ed5779b07

import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_000_100
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_100_200
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_200_300
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_300_400
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_400_500
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_pairs_500_533
import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ p ∈ lowerEarlyTerminalTerminal3.pairs, lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p := by
  have he : lowerEarlyTerminalTerminal3.pairs = (lowerEarlyTerminalTerminal3.pairs.drop 0).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 100).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 200).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 300).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 400).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 500).take 33 := by rfl
  have hc : ∀ p ∈ ((lowerEarlyTerminalTerminal3.pairs.drop 0).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 100).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 200).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 300).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 400).take 100 ++ (lowerEarlyTerminalTerminal3.pairs.drop 500).take 33), lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p :=
    List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_terminal3_pairs_000_100, Freiman.lowerEarlyTerminal_terminal3_pairs_100_200⟩, Freiman.lowerEarlyTerminal_terminal3_pairs_200_300⟩, Freiman.lowerEarlyTerminal_terminal3_pairs_300_400⟩, Freiman.lowerEarlyTerminal_terminal3_pairs_400_500⟩, Freiman.lowerEarlyTerminal_terminal3_pairs_500_533⟩
  exact Eq.mpr (congrArg (fun ps : List LowerEarlyTerminalPair => ∀ p ∈ ps, lowerEarlyTerminalPairValid lowerEarlyTerminalTerminal3 p) he) hc

#print axioms solution
