-- Prove2me | solution 1 for FriedCrossing.Scale.derivLoss_eq_derivSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:34.881192+00:00
-- url     : https://prove2.me/submissions/4497b316-75b6-4cdb-a397-299621f60601

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
theorem _root_.solution (a b : ℕ) (hab : b + 2 ≤ a) (x : X) :
    derivLoss F a b hab x = derivSplit F a b 1 hab x := rfl
end FriedCrossing.Scale
