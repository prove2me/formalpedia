-- Prove2me | solution 1 for FongoSync.live_iff_liveAt_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:50.340803+00:00
-- url     : https://prove2.me/submissions/eba5da84-21d2-48d9-9f0c-00a4de236454

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
import Theorems.Thm_FongoSync_liveAt_mono
import Theorems.Thm_FongoSync_liveAt_stable
import Theorems.Thm_FongoSync_exists_stable

set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)
namespace FongoSync
theorem _root_.solution (g : Gid) : Live sc inp g ↔ liveAt sc inp inp.gids.length g := by
  obtain ⟨k, hk, hs⟩ := exists_stable sc inp
  have stable : ∀ j, liveAt sc inp j g → liveAt sc inp k g := by
    intro j hj
    rcases Nat.le_total j k with hjk | hkj
    · exact liveAt_mono sc inp hjk hj
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
      exact (liveAt_stable sc inp hs d g).mp hj
  constructor
  · rintro ⟨j, hj⟩; exact liveAt_mono sc inp hk (stable j hj)
  · intro h; exact ⟨_, h⟩
end FongoSync
