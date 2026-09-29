-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_short_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:54.164521+00:00
-- url     : https://prove2.me/submissions/e514b8c4-88a0-452c-b4ce-9ec0ff4ea31e

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order
import Theorems.Thm_Freiman_lowerEarlyTerminal_cross_contact
import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness
import Theorems.Thm_Freiman_lowerEarlyTerminal_short_contacts
import Theorems.Thm_Freiman_lowerEarlyTerminal_short_goodness
import Theorems.Thm_Freiman_lowerEarlyTerminal_short_gluing
import Theorems.Thm_Freiman_lowerEarlyTerminal_anchor_goodness
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerEarlyTerminal_cover_nonempty

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (mode : ℕ) (hm : mode<2) (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p mode)
    (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode)) :
    lowerEarlyTerminalListGeometry p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  have ho := lowerEarlyTerminal_endpoint_order
  have hc := lowerEarlyTerminal_cross_contact p
  have hg := lowerEarlyTerminal_child_goodness t p hs hd
  exact lowerEarlyTerminal_short_gluing p mode hm
    ⟨lowerEarlyTerminal_short_goodness C p mode hm hb h ha lowerEarlyTerminal_cover_nonempty
        (fun l hn hl => hg l hn lowerHistory_width_threshold ho hl) (lowerEarlyTerminal_anchor_goodness t p hs hd),
      lowerEarlyTerminal_short_contacts C p mode hm h ha ho
        (fun a b h1 h2 => hc a b ho h1 h2)⟩
