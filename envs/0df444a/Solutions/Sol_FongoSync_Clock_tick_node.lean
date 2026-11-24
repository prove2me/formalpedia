-- Prove2me | solution 1 for FongoSync.Clock.tick_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:59.970412+00:00
-- url     : https://prove2.me/submissions/82e44f6e-1159-49e2-8e75-7e72a1bf8b22


import Definitions.Def_FongoSync_Clock

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (wall : Nat) : (c.tick wall).1.node = c.last.node := by
  unfold Clock.tick; simp only; split
  · rfl
  · split <;> rfl
end Clock
end FongoSync
