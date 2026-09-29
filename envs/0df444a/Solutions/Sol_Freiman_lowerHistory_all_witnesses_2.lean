-- Prove2me | solution 2 for Freiman.lowerHistory_all_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:29:59.419977+00:00
-- url     : https://prove2.me/submissions/d0ff4fce-7f2f-40bb-882e-af7a95abc628

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_inventory_sizes
import Theorems.Thm_Freiman_lowerHistory_witnesses_0000_0100
import Theorems.Thm_Freiman_lowerHistory_witnesses_0100_0200
import Theorems.Thm_Freiman_lowerHistory_witnesses_0200_0300
import Theorems.Thm_Freiman_lowerHistory_witnesses_0300_0400
import Theorems.Thm_Freiman_lowerHistory_witnesses_0400_0500
import Theorems.Thm_Freiman_lowerHistory_witnesses_0500_0600
import Theorems.Thm_Freiman_lowerHistory_witnesses_0600_0700
import Theorems.Thm_Freiman_lowerHistory_witnesses_0700_0800
import Theorems.Thm_Freiman_lowerHistory_witnesses_0800_0900
import Theorems.Thm_Freiman_lowerHistory_witnesses_0900_1000
import Theorems.Thm_Freiman_lowerHistory_witnesses_1000_1100
import Theorems.Thm_Freiman_lowerHistory_witnesses_1100_1194
import Theorems.Thm_Freiman_lowerHistory_join_witnesses

open Freiman

-- `lowerHistory_join_witnesses` rebuilds the whole-catalogue witness statement from
-- the size triple plus the twelve hundred-ranges; all of those are now separate nodes.
theorem solution : lowerHistoryAllWitnesses :=
  lowerHistory_join_witnesses lowerHistory_inventory_sizes
    lowerHistory_witnesses_0000_0100
    lowerHistory_witnesses_0100_0200
    lowerHistory_witnesses_0200_0300
    lowerHistory_witnesses_0300_0400
    lowerHistory_witnesses_0400_0500
    lowerHistory_witnesses_0500_0600
    lowerHistory_witnesses_0600_0700
    lowerHistory_witnesses_0700_0800
    lowerHistory_witnesses_0800_0900
    lowerHistory_witnesses_0900_1000
    lowerHistory_witnesses_1000_1100
    lowerHistory_witnesses_1100_1194
