-- Prove2me | solution 1 for FriedCrossing.Scale.B_incl_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:39.813408+00:00
-- url     : https://prove2.me/submissions/2ed6845a-6a2b-470b-a952-aec49e1e549d

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
theorem _root_.solution (a b : ℕ) (hab : b ≤ a) (x : X) :
    (S.incl a b hab).comp (F.B a x) = (F.B b x).comp (S.incl (a + 1) (b + 1) (by omega)) := by
  induction a with
  | zero =>
    have hb : b = 0 := Nat.le_zero.mp hab
    subst hb
    rw [S.incl_refl, S.incl_refl]; simp
  | succ a ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · subst h; rw [S.incl_refl, S.incl_refl]; simp
    · have hba : b ≤ a := Nat.lt_succ_iff.mp h
      rw [← S.incl_trans (a + 1) a b (Nat.le_succ a) hba, comp_assoc, F.B_incl, ← comp_assoc,
        ih hba, comp_assoc, S.incl_trans]
end FriedCrossing.Scale
