-- Prove2me | solution 1 for DeletionCode.SelectedWindows.Realizes.start_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:11.683083+00:00
-- url     : https://prove2.me/submissions/fe81a6a6-7eec-4bbe-b039-610a2f9c5305

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_update_mem

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
variable {B : Type*}
namespace DeletionCode.SelectedWindows
namespace Realizes
theorem _root_.solution [DecidableEq B] (s : State B) (mem : B → Memory)
    (D : B → ℕ) (k : ℕ) (hreal : Realizes s mem D k) (b : B) (w : Slot) (t : Memory)
    (hext : Extends (mem b) t)
    (hseed : SeedKnown t (windowStart (D b) w) (3 * (k + 1)) k) :
    Realizes (s.start b w) (Function.update mem b t) D k := by
  apply Realizes.start s (Function.update mem b t) D k
    (Realizes.update_mem s mem D k hreal b t hext) b w
  simpa using hseed
end Realizes
end DeletionCode.SelectedWindows
