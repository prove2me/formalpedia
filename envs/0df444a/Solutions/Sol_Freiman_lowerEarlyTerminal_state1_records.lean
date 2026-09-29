-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state1_records
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:21:58.392916+00:00
-- url     : https://prove2.me/submissions/2ecf0ab7-0334-4713-8fd2-70eeca5e2ae1

import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_records_shard1
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_records_shard2
import Theorems.Thm_Freiman_lowerEarlyTerminal_state1_records_shard3
import Definitions.Def_Freiman_lowerEarlyTerminalDataState1
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ r ∈ lowerEarlyTerminalState1.records, lowerEarlyTerminalRecordValid lowerEarlyTerminalState1 r := by
  exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_state1_records_shard1, Freiman.lowerEarlyTerminal_state1_records_shard2⟩, Freiman.lowerEarlyTerminal_state1_records_shard3⟩

#print axioms solution
