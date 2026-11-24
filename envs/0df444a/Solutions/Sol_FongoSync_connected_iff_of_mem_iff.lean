-- Prove2me | solution 1 for FongoSync.connected_iff_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:07:28.429803+00:00
-- url     : https://prove2.me/submissions/097fd521-b6a9-4f71-b11e-6e382c0e33fb

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_Connected_mono

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {E₁ E₂ : List Edge} (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) (a b : Gid) :
    Connected E₁ a b ↔ Connected E₂ a b :=
  ⟨fun h => h.mono fun e he => (same e).mp he, fun h => h.mono fun e he => (same e).mpr he⟩
end FongoSync
