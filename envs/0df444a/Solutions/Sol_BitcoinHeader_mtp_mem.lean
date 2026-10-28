-- Prove2me | solution 1 for BitcoinHeader.mtp_mem
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:11.354172+00:00
-- url     : https://prove2.me/submissions/f9285b52-56f0-4d68-8011-61137470f546

import Definitions.Def_BitcoinHeader
import Theorems.Thm_BitcoinHeader_mtp_mem_window

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ times :=
  List.mem_of_mem_take (BitcoinHeader.mtp_mem_window times h)
