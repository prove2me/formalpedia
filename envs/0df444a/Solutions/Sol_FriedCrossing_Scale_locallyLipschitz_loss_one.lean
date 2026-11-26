-- Prove2me | solution 1 for FriedCrossing.Scale.locallyLipschitz_loss_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:52:38.212842+00:00
-- url     : https://prove2.me/submissions/19ff4629-8f0c-45e0-9c2e-78842bbfdf15

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_resolvent_identity

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (n : ℕ) :
    LocallyLipschitz fun x => (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x) := by
  intro x₀
  obtain ⟨C, hC⟩ := F.bdd n x₀
  obtain ⟨C', hC'⟩ := F.bdd (n + 1) x₀
  obtain ⟨K, t, ht, hK⟩ := (F.smooth n).of_le le_top |>.locallyLipschitz x₀
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hC.self_of_nhds
  have hC'0 : 0 ≤ C' := le_trans (norm_nonneg _) hC'.self_of_nhds
  refine ⟨⟨C * K * C', by positivity⟩, {x | ‖F.R n x‖ ≤ C} ∩ {x | ‖F.R (n + 1) x‖ ≤ C'} ∩ t,
    inter_mem (inter_mem hC hC') ht, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  obtain ⟨⟨hxC, hxC'⟩, hxt⟩ := hx
  obtain ⟨⟨hyC, hyC'⟩, hyt⟩ := hy
  rw [dist_eq_norm, ← comp_sub, resolvent_identity]
  calc ‖((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y)‖
      ≤ ‖(F.R n x).comp (F.B n y - F.B n x)‖ * ‖F.R (n + 1) y‖ := opNorm_comp_le _ _
    _ ≤ ‖F.R n x‖ * ‖F.B n y - F.B n x‖ * ‖F.R (n + 1) y‖ := by
        gcongr; exact opNorm_comp_le _ _
    _ ≤ C * (K * dist x y) * C' := by
        have h1 : ‖F.R n x‖ ≤ C := hxC
        have h2 : ‖F.B n y - F.B n x‖ ≤ K * dist x y := by
          rw [← dist_eq_norm, dist_comm]; exact hK.dist_le_mul x hxt y hyt
        have h3 : ‖F.R (n + 1) y‖ ≤ C' := hyC'
        exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hC0) h3 (norm_nonneg _)
          (mul_nonneg hC0 (by positivity))
    _ = ((⟨C * K * C', by positivity⟩ : NNReal) : ℝ) * dist x y := by push_cast; ring
end FriedCrossing.Scale
