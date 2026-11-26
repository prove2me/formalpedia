-- Prove2me | solution 1 for FriedCrossing.Scale.contDiff_derivSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:18.077991+00:00
-- url     : https://prove2.me/submissions/37ca7cc8-8db2-4b69-a01c-53a78615bc6a

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
theorem _root_.solution (k : ℕ) (a b j : ℕ) (hj : b + j + 1 ≤ a)
    (hU : ContDiff ℝ k fun x => (S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x))
    (hV : ContDiff ℝ k fun x => (S.incl a (b + j + 1) hj).comp (F.R a x)) :
    ContDiff ℝ k fun x => derivSplit F a b j hj x := by
  have hW : ContDiff ℝ k (fderiv ℝ (F.B (b + j))) := (F.smooth (b + j)).fderiv_right le_top
  have h1 : ContDiff ℝ k fun x => (compL ℝ (S.H a) (S.H (b + j)) (S.H b))
      ((S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x)) :=
    contDiff_const.clm_apply hU
  have h2 : ContDiff ℝ k fun x => (compL ℝ (S.H a) (S.H (b + j + 1)) (S.H (b + j))).flip
      ((S.incl a (b + j + 1) hj).comp (F.R a x)) :=
    contDiff_const.clm_apply hV
  exact (h1.clm_comp (h2.clm_comp hW)).neg
end FriedCrossing.Scale
