-- Prove2me | solution 1 for FongoSync.Clock.tick_after_any_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:32.730796+00:00
-- url     : https://prove2.me/submissions/586959c6-8567-45d8-bf96-a161110c0d9a


import Definitions.Def_FongoSync_Clock
import Theorems.Thm_FongoSync_Hlc_lt_of_before
import Theorems.Thm_FongoSync_Hlc_before_of_notAfter_of_before
import Theorems.Thm_FongoSync_Clock_tick_before
import Theorems.Thm_FongoSync_Clock_run_notAfter

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (events : List Event) (wall : Nat) :
    c.last < ((c.run events).1.tick wall).1 ∧
      ∀ r ∈ (c.run events).2, r < ((c.run events).1.tick wall).1 := by
  have ⟨h₁, h₂⟩ := c.run_notAfter events
  have t := (c.run events).1.tick_before wall
  exact ⟨Hlc.lt_of_before (Hlc.before_of_notAfter_of_before h₁ t),
    fun r hr => Hlc.lt_of_before (Hlc.before_of_notAfter_of_before (h₂ r hr) t)⟩
end Clock
end FongoSync
