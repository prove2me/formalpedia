-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_state2_records
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T21:22:04.663646+00:00
-- url     : https://prove2.me/submissions/e1d806d1-1b9c-4e5f-935b-bb1bf0c88dab

import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_records_shard1
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_records_shard2
import Theorems.Thm_Freiman_lowerEarlyTerminal_state2_records_shard3
import Definitions.Def_Freiman_lowerEarlyTerminalDataState2
import Mathlib.Data.Fintype.Basic
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ r ∈ lowerEarlyTerminalState2.records, lowerEarlyTerminalRecordValid lowerEarlyTerminalState2 r := by
  exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨Freiman.lowerEarlyTerminal_state2_records_shard1, Freiman.lowerEarlyTerminal_state2_records_shard2⟩, Freiman.lowerEarlyTerminal_state2_records_shard3⟩

#print axioms solution
