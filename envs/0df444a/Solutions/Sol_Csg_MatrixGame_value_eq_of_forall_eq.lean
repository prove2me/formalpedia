-- Prove2me | solution 1 for Csg.MatrixGame.value_eq_of_forall_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:35:05.785708+00:00
-- url     : https://prove2.me/submissions/b4d05f90-b172-4430-8bc6-c3475e81092a

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
import Theorems.Thm_Csg_MatrixGame_le_value_of_forall_le
import Theorems.Thm_Csg_MatrixGame_value_le_of_forall_le


set_option autoImplicit true
open Csg Csg.MatrixGame
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I]
  [DecidableEq J] (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {c : ℝ} (h : ∀ i j, G.A i j = c) : G.value = c :=
  le_antisymm (G.value_le_of_forall_le fun i j => (h i j).le)
    (G.le_value_of_forall_le fun i j => (h i j).ge)
end Csg.MatrixGame
