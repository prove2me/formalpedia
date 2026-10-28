-- Prove2me | solution 1 for BitcoinHeader.mtp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:11.908556+00:00
-- url     : https://prove2.me/submissions/88695db7-575d-4c35-80b4-b8cd59e9acbf

import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_mtp_mem_window

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) (lo hi : Int)
    (hb : ∀ t ∈ BitcoinHeader.timeWindow times, lo ≤ t ∧ t ≤ hi) :
    lo ≤ BitcoinHeader.medianTimePast times ∧ BitcoinHeader.medianTimePast times ≤ hi :=
  hb _ (BitcoinHeader.mtp_mem_window times h)
