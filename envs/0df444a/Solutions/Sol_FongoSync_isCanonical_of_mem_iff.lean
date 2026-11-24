-- Prove2me | solution 1 for FongoSync.isCanonical_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:12.762428+00:00
-- url     : https://prove2.me/submissions/f8b0c486-6f75-482c-80c6-bb8a504b3381

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
import Theorems.Thm_FongoSync_Connected_mono

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution {E₁ E₂ : List Edge} (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) {g r : Gid}
    (h : IsCanonical E₁ g r) : IsCanonical E₂ g r :=
  ⟨h.1.mono fun e he => (same e).mp he,
   fun x c => h.2 x (c.mono fun e he => (same e).mpr he)⟩
end FongoSync
