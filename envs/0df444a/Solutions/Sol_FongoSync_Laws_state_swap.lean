-- Prove2me | solution 1 for FongoSync.Laws.state_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:34.643287+00:00
-- url     : https://prove2.me/submissions/c1e95339-7617-4673-91e9-3214dafb4d43

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_State_foldl_swap


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a b : Change V) (h : Compatible a b) :
    (pre ++ a :: b :: post).foldl (State.apply σ) st =
      (pre ++ b :: a :: post).foldl (State.apply σ) st :=
  State.foldl_swap σ st pre post a b h
end FongoSync.Laws
