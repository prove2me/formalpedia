-- Prove2me | solution 1 for FriedCrossing.Scale.contDiff_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:25.839176+00:00
-- url     : https://prove2.me/submissions/4e1f964e-54bb-436c-9d3d-d23476f6e2df

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_continuous_loss
import Theorems.Thm_FriedCrossing_Scale_hasFDerivAt_loss
import Theorems.Thm_FriedCrossing_Scale_one_le_lossBudget
import Theorems.Thm_FriedCrossing_Scale_derivSplit_apply_canonical
import Theorems.Thm_FriedCrossing_Scale_derivLoss_eq_derivSplit
import Theorems.Thm_FriedCrossing_Scale_contDiff_derivSplit

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution : ∀ (k : ℕ) (a b : ℕ) (hab : b + lossBudget k ≤ a),
    ContDiff ℝ k fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp (F.R a x) := by
  intro k
  induction k with
  | zero =>
    intro a b hab
    simp only [Nat.cast_zero, contDiff_zero]
    exact continuous_loss F a b (by simpa [lossBudget] using hab)
  | succ k ih =>
    intro a b hab
    have hL1 := one_le_lossBudget k
    have hab2 : b + 2 ≤ a := by simp only [lossBudget] at hab; omega
    have hd : ∀ x, HasFDerivAt
        (fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp (F.R a x))
        (derivLoss F a b hab2 x) x := hasFDerivAt_loss F a b hab2
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
    have hj : b + lossBudget k + 1 ≤ a := by simp only [lossBudget] at hab; omega
    have hfd : fderiv ℝ (fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp
        (F.R a x)) = fun x => derivSplit F a b (lossBudget k) hj x := by
      funext x
      rw [(hd x).fderiv, derivLoss_eq_derivSplit]
      ext h
      rw [derivSplit_apply_canonical, derivSplit_apply_canonical]
    rw [hfd]
    exact contDiff_derivSplit F k a b (lossBudget k) hj (ih (b + lossBudget k) b le_rfl)
      (ih a (b + lossBudget k + 1) (by simp only [lossBudget] at hab; omega))
end FriedCrossing.Scale
