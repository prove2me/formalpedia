-- Prove2me | solution 1 for FriedCrossing.Scale.derivSplit_apply_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:44.295593+00:00
-- url     : https://prove2.me/submissions/209a06e7-a90a-4f03-9fd9-b13a40d736a6

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_R_incl_gen
import Theorems.Thm_FriedCrossing_Scale_fderiv_B_incl_gen

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (a b j : ℕ) (hj : b + j + 1 ≤ a) (x h : X) :
    derivSplit F a b j hj x h =
      -((F.R b x).comp ((fderiv ℝ (F.B b) x h).comp
        ((S.incl a (b + 1) (by omega)).comp (F.R a x)))) := by
  simp only [derivSplit, neg_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply]
  congr 1
  -- left-associate, then push the inclusions through R and ∂B
  rw [← comp_assoc, ← comp_assoc, R_incl_gen F (b + j) b (Nat.le_add_right b j) x,
    comp_assoc (F.R b x), fderiv_B_incl_gen F (b + j) b (Nat.le_add_right b j) x h,
    comp_assoc (F.R b x), comp_assoc (fderiv ℝ (F.B b) x h), S.incl_trans]
  simp only [comp_assoc]
end FriedCrossing.Scale
