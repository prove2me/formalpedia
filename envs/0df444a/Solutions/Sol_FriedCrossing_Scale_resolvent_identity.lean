-- Prove2me | solution 1 for FriedCrossing.Scale.resolvent_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:51:35.607151+00:00
-- url     : https://prove2.me/submissions/81ff8741-e63e-42f2-94f2-08f2ee0ee888

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (n : ℕ) (x y : X) :
    (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x - F.R (n + 1) y) =
      ((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y) := by
  have h1 : ((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y) =
      (F.R n x).comp ((F.B n y).comp (F.R (n + 1) y)) -
        ((F.R n x).comp (F.B n x)).comp (F.R (n + 1) y) := by
    rw [comp_sub, sub_comp, comp_assoc]
  rw [h1, F.inv_right, F.inv_left, ← F.R_incl, comp_sub]
end FriedCrossing.Scale
