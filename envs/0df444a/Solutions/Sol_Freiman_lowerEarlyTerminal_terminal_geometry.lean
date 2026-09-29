-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_terminal_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:54.438101+00:00
-- url     : https://prove2.me/submissions/a3de21aa-6a3e-4a74-9d8d-8ece046210cd

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order
import Theorems.Thm_Freiman_lowerEarlyTerminal_cross_contact
import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_goodness
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_contacts
import Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_gluing
import Theorems.Thm_Freiman_lowerEarlyTerminal_union_contact
import Theorems.Thm_Freiman_lowerEarlyTerminal_parameter_laws
import Theorems.Thm_Freiman_lowerEarlyTerminal_anchor_goodness
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lowerEarlyTerminal_cover_nonempty

open Freiman

open Classical

theorem solution (C : LowerEarlyTerminalCatalog) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2)) :
    lowerEarlyTerminalListGeometry p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p)) := by
  have ho := lowerEarlyTerminal_endpoint_order
  have hg := lowerEarlyTerminal_child_goodness t p hs hd
  have hl := lowerEarlyTerminal_terminal_goodness lowerEarlyTerminal_parameter_laws C p h27 h34 h ha lowerEarlyTerminal_cover_nonempty
    (fun l hn hh => hg l hn lowerHistory_width_threshold ho hh) (lowerEarlyTerminal_anchor_goodness t p hs hd)
  exact lowerEarlyTerminal_terminal_gluing p (lowerEarlyTerminalPrimary p)
    (lowerEarlyTerminal_terminal_contacts lowerEarlyTerminal_parameter_laws C p h ha ho
      (fun a b h1 h2 => lowerEarlyTerminal_cross_contact p a b ho h1 h2)
      (fun a b c hh h1 h2 => lowerEarlyTerminal_union_contact p a b c ho hh h1 h2) hl)
