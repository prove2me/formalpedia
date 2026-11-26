-- Prove2me | solution 1 for FriedCrossing.Scale.continuous_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:58.632201+00:00
-- url     : https://prove2.me/submissions/da50a722-b97b-4a1e-803f-f79c6c708b3b

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_R_incl_gen
import Theorems.Thm_FriedCrossing_Scale_locallyLipschitz_loss_one

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (a b : ℕ) (hab : b + 1 ≤ a) :
    Continuous fun x => (S.incl a b (by omega)).comp (F.R a x) := by
  have heq : (fun x => (S.incl a b (by omega)).comp (F.R a x)) =
      fun x => ((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        (S.incl a (b + 1) hab) := by
    funext x
    rw [comp_assoc, ← R_incl_gen F a (b + 1) hab, ← comp_assoc, S.incl_trans]
  rw [heq]
  exact (locallyLipschitz_loss_one F b).continuous.clm_comp continuous_const
end FriedCrossing.Scale
