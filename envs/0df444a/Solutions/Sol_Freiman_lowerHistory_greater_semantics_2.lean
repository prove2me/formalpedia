-- Prove2me | solution 2 for Freiman.lowerHistory_greater_semantics
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:21:57.315109+00:00
-- url     : https://prove2.me/submissions/aacbc2fb-0879-41c2-82f5-7aefbcf8632e

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_greater_from_sign
import Theorems.Thm_Freiman_lowerHistory_sign_value

open Freiman

theorem solution : LowerHistoryGreaterLaw := by
  intro base C hc x y hx hy
  exact lowerHistory_greater_from_sign
    (fun z => lowerHistory_sign_value z) base C hc x y hx hy
