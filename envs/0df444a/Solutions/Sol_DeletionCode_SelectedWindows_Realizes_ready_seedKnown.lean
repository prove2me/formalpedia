-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.ready_seedKnown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:59.291713+00:00
-- url     : https://prove2.me/submissions/51a585bc-edd9-41bc-b46e-77db7df890aa

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_adjacent_window_seed

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution (s : State B) (mem : B → Memory) (D : B → ℕ)
    (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot)
    (hD : D b < 3 * (k + 1)) (hready : s.Ready b w) :
    SeedKnown (mem b) (windowStart (D b) w) (3 * (k + 1)) k := by
  rcases hready with hseed | ⟨v, hv, hadj⟩
  · exact hreal.seed_known b w hseed
  · exact adjacent_window_seed (mem b) (D b) k v w hD hadj (hreal.done_known b v hv)
end Realizes
end DeletionCode.SelectedWindows
