-- Prove2me | solution 2 for Freiman.lowerEarlyTerminal_state1_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:21:32.303278+00:00
-- url     : https://prove2.me/submissions/99577608-614a-4956-a41d-d50350eb89e5

import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_000_100
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_100_200
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_200_300
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_300_400
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_400_500
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_500_600
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_600_700
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_pairs_700_743
import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ p ∈ lowerEarlyTerminalState1.pairs, lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p := by
  have he : lowerEarlyTerminalState1.pairs = (lowerEarlyTerminalState1.pairs.drop 0).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 100).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 200).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 300).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 400).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 500).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 600).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 700).take 43 := by rfl
  have hc : ∀ p ∈ ((lowerEarlyTerminalState1.pairs.drop 0).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 100).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 200).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 300).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 400).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 500).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 600).take 100 ++ (lowerEarlyTerminalState1.pairs.drop 700).take 43), lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p :=
    List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_state1_pairs_000_100, Freiman.lowerEarlyTerminal_state1_pairs_100_200⟩, Freiman.lowerEarlyTerminal_state1_pairs_200_300⟩, Freiman.lowerEarlyTerminal_state1_pairs_300_400⟩, Freiman.lowerEarlyTerminal_state1_pairs_400_500⟩, Freiman.lowerEarlyTerminal_state1_pairs_500_600⟩, Freiman.lowerEarlyTerminal_state1_pairs_600_700⟩, Freiman.lowerEarlyTerminal_state1_pairs_700_743⟩
  exact Eq.mpr (congrArg (fun ps : List LowerEarlyTerminalPair => ∀ p ∈ ps, lowerEarlyTerminalPairValid lowerEarlyTerminalState1 p) he) hc

#print axioms solution
