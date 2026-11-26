-- Prove2me | solution 1 for FriedCrossing.Scale.fderiv_B_incl_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:46.801922+00:00
-- url     : https://prove2.me/submissions/cd5b4b91-e428-4ba2-bfc2-26c70c08a545

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_B_incl_gen

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (a b : ℕ) (hab : b ≤ a) (x h : X) :
    (S.incl a b hab).comp (fderiv ℝ (F.B a) x h) =
      (fderiv ℝ (F.B b) x h).comp (S.incl (a + 1) (b + 1) (by omega)) := by
  have hBa : HasFDerivAt (F.B a) (fderiv ℝ (F.B a) x) x :=
    ((F.smooth a).differentiable (by simp) x).hasFDerivAt
  have hBb : HasFDerivAt (F.B b) (fderiv ℝ (F.B b) x) x :=
    ((F.smooth b).differentiable (by simp) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => (S.incl a b hab).comp (F.B a y))
      ((compL ℝ (S.H (a + 1)) (S.H a) (S.H b) (S.incl a b hab)).comp (fderiv ℝ (F.B a) x)) x := by
    have := (compL ℝ (S.H (a + 1)) (S.H a) (S.H b) (S.incl a b hab)).hasFDerivAt.comp x hBa
    simpa [Function.comp_def, compL_apply] using this
  have h2 : HasFDerivAt (fun y => (F.B b y).comp (S.incl (a + 1) (b + 1) (by omega)))
      (((compL ℝ (S.H (a + 1)) (S.H (b + 1)) (S.H b)).flip
        (S.incl (a + 1) (b + 1) (by omega))).comp (fderiv ℝ (F.B b) x)) x := by
    have := ((compL ℝ (S.H (a + 1)) (S.H (b + 1)) (S.H b)).flip
      (S.incl (a + 1) (b + 1) (by omega))).hasFDerivAt.comp x hBb
    simpa [Function.comp_def, compL_apply, flip_apply] using this
  have hfun : (fun y => (S.incl a b hab).comp (F.B a y)) =
      fun y => (F.B b y).comp (S.incl (a + 1) (b + 1) (by omega)) :=
    funext fun y => B_incl_gen F a b hab y
  rw [hfun] at h1
  have := congrArg (fun T => T h) (h1.unique h2)
  simpa [compL_apply, flip_apply] using this
end FriedCrossing.Scale
