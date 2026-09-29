-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_record_sound
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:39:45.462988+00:00
-- url     : https://prove2.me/submissions/57c8cf1d-f93e-4f7b-91be-5eb91d479e6a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem solution (C : LowerEarlyTerminalCatalog) (hp : lowerEarlyTerminalPairSound C) (rec : LowerEarlyTerminalRecord) (hr : lowerEarlyTerminalRecordValid C rec) : lowerEarlyTerminalRecordSound C rec := by
  intro r s q hmem hhold
  obtain ⟨-, hpair, -, -, hfin, hlo, hup⟩ := hr
  have hpm : lowerEarlyTerminalPair C rec.pairId ∈ C.pairs := by
    unfold lowerEarlyTerminalPair
    rw [List.getElem?_eq_getElem hpair]
    exact List.getElem_mem _
  apply hp _ hpm r s q hmem
  have hsub : ∀ b ∈ lowerEarlyTerminalBoundsAt C rec.premises, certBoundHolds b r s q := by
    intro b hb
    apply hhold
    have : b ∈ (lowerEarlyTerminalBoundsAt C rec.premises).toFinset := List.mem_toFinset.2 hb
    rw [hfin] at this
    exact List.mem_toFinset.1 this
  exact ⟨hsub _ (List.mem_map.2 ⟨_, hlo, rfl⟩), hsub _ (List.mem_map.2 ⟨_, hup, rfl⟩)⟩
