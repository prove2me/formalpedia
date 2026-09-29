-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal3_records
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-14T00:12:42.442944+00:00
-- url     : https://prove2.me/submissions/20d05591-21e0-4935-a14d-7b3e81ba5889

import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_records_shard1
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal3_records_shard2
import Definitions.Def_Freiman_lowerEarlyTerminalDataTerminal3
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ r ∈ lowerEarlyTerminalTerminal3.records, lowerEarlyTerminalRecordValid lowerEarlyTerminalTerminal3 r := by
  exact List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_terminal3_records_shard1, Freiman.lowerEarlyTerminal_terminal3_records_shard2⟩

#print axioms solution
