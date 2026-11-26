-- Prove2me | solution 1 for FriedCrossing.Scale.diff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:09.606343+00:00
-- url     : https://prove2.me/submissions/8a3e6b2d-6592-483d-802b-2e3d6df90c63

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_resolvent_identity
import Theorems.Thm_FriedCrossing_Scale_R_incl_gen

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (a b : ℕ) (hab : b + 2 ≤ a) (x x₀ : X) :
    (S.incl a b (by omega)).comp (F.R a x - F.R a x₀) =
      (((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        (F.B (b + 1) x₀ - F.B (b + 1) x)).comp ((S.incl a (b + 2) hab).comp (F.R a x₀)) := by
  have h1 : (S.incl a b (by omega)).comp (F.R a x - F.R a x₀) =
      (S.incl (b + 1) b (Nat.le_succ b)).comp
        (((S.incl (b + 2) (b + 1) (Nat.le_succ _)).comp (F.R (b + 2) x - F.R (b + 2) x₀)).comp
          (S.incl a (b + 2) hab)) := by
    rw [comp_assoc, sub_comp, ← R_incl_gen F a (b + 2) hab x, ← R_incl_gen F a (b + 2) hab x₀,
      ← comp_sub, ← comp_assoc, ← comp_assoc, S.incl_trans, S.incl_trans]
  rw [h1, resolvent_identity]
  simp only [comp_assoc]
  rw [R_incl_gen F a (b + 2) hab x₀]
end FriedCrossing.Scale
