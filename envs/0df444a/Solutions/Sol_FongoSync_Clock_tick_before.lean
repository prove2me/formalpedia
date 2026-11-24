-- Prove2me | solution 1 for FongoSync.Clock.tick_before
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:05.574989+00:00
-- url     : https://prove2.me/submissions/c80e5c68-143d-4a0b-a7a4-f350a08f604c


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (wall : Nat) : c.last.Before (c.tick wall).1 := by
  unfold Clock.tick Hlc.Before
  simp only
  split
  · simp_all
  · split <;> simp <;> omega
end Clock
end FongoSync
