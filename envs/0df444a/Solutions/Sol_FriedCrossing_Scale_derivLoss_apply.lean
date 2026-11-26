-- Prove2me | solution 1 for FriedCrossing.Scale.derivLoss_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:09.000826+00:00
-- url     : https://prove2.me/submissions/c057c74c-818f-4fa0-a234-6cec30841a21

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
theorem _root_.solution (a b : ℕ) (hab : b + 2 ≤ a) (x : X) (h : X) :
    derivLoss F a b hab x h =
      -(((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        ((fderiv ℝ (F.B (b + 1)) x h).comp ((S.incl a (b + 2) hab).comp (F.R a x)))) := by
  simp [derivLoss, compL_apply, flip_apply]
end FriedCrossing.Scale
