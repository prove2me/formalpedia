-- Prove2me | solution 1 for FongoSync.Laws.state_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:35.122452+00:00
-- url     : https://prove2.me/submissions/e9791919-3ea7-4bed-8014-9fa1ae4f5c87

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_State_foldl_twice


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a : Change V) :
    (pre ++ a :: a :: post).foldl (State.apply σ) st =
      (pre ++ a :: post).foldl (State.apply σ) st :=
  State.foldl_twice σ st pre post a
end FongoSync.Laws
