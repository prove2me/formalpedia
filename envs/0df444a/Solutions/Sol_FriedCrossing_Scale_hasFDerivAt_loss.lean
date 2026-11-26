-- Prove2me | solution 1 for FriedCrossing.Scale.hasFDerivAt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:28.648486+00:00
-- url     : https://prove2.me/submissions/565705af-5907-4b23-9aea-186a7b88de51

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
import Theorems.Thm_FriedCrossing_Scale_locallyLipschitz_loss_one
import Theorems.Thm_FriedCrossing_Scale_derivLoss_apply
import Theorems.Thm_FriedCrossing_Scale_diff_eq

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)
namespace FriedCrossing.Scale
theorem _root_.solution (a b : ℕ) (hab : b + 2 ≤ a) (x₀ : X) :
    HasFDerivAt (fun x => (S.incl a b (by omega)).comp (F.R a x)) (derivLoss F a b hab x₀) x₀ := by
  set U : X → (S.H (b + 1) →L[ℝ] S.H b) :=
    fun x => (S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x) with hU
  set V : S.H a →L[ℝ] S.H (b + 2) := (S.incl a (b + 2) hab).comp (F.R a x₀) with hV
  -- Lipschitz data for U near x₀, Lipschitz data for B (b+1) near x₀
  obtain ⟨K, t, ht, hK⟩ := locallyLipschitz_loss_one F b x₀
  obtain ⟨K', t', ht', hK'⟩ := (F.smooth (b + 1)).of_le le_top |>.locallyLipschitz x₀
  have hBd : HasFDerivAt (F.B (b + 1)) (fderiv ℝ (F.B (b + 1)) x₀) x₀ :=
    ((F.smooth (b + 1)).differentiable (by simp) x₀).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- the error splits as e₁ + e₂
  have hsplit : ∀ h : X,
      (S.incl a b (by omega)).comp (F.R a (x₀ + h)) - (S.incl a b (by omega)).comp (F.R a x₀) -
        derivLoss F a b hab x₀ h =
      ((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V -
        ((U x₀).comp
          (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V := by
    intro h
    rw [← comp_sub, diff_eq F a b hab (x₀ + h) x₀, derivLoss_apply]
    simp only [hU, hV, sub_comp, comp_sub, comp_assoc, sub_neg_eq_add]
    abel
  have he₁ : (fun h : X =>
      ((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V)
      =o[𝓝 0] fun h => h := by
    have hbig : (fun h : X => ((U (x₀ + h) - U x₀).comp
        (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V) =O[𝓝 0] fun h => ‖h‖ ^ 2 := by
      have hmem : ∀ᶠ h : X in 𝓝 0, x₀ + h ∈ t ∩ t' := by
        have : Tendsto (fun h : X => x₀ + h) (𝓝 0) (𝓝 x₀) := by
          simpa using (tendsto_id (x := 𝓝 (0 : X))).const_add x₀
        exact this (inter_mem ht ht')
      refine IsBigO.of_bound (K * K' * ‖V‖) ?_
      filter_upwards [hmem] with h hh
      have hUl : ‖U (x₀ + h) - U x₀‖ ≤ K * ‖h‖ := by
        have := hK.dist_le_mul (x₀ + h) hh.1 x₀ (mem_of_mem_nhds ht)
        rwa [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at this
      have hBl : ‖F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h)‖ ≤ K' * ‖h‖ := by
        have := hK'.dist_le_mul x₀ (mem_of_mem_nhds ht') (x₀ + h) hh.2
        rwa [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg] at this
      calc ‖((U (x₀ + h) - U x₀).comp (F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h))).comp V‖
          ≤ ‖U (x₀ + h) - U x₀‖ * ‖F.B (b + 1) x₀ - F.B (b + 1) (x₀ + h)‖ * ‖V‖ := by
            refine le_trans (opNorm_comp_le _ _) ?_
            gcongr; exact opNorm_comp_le _ _
        _ ≤ (K * ‖h‖) * (K' * ‖h‖) * ‖V‖ := by gcongr
        _ = K * K' * ‖V‖ * ‖‖h‖ ^ 2‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    exact hbig.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
  have he₂ : (fun h : X => ((U x₀).comp
      (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V)
      =o[𝓝 0] fun h => h := by
    have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hBd
    have hbig : (fun h : X => ((U x₀).comp
        (F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h)).comp V) =O[𝓝 0]
        fun h => F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h := by
      refine IsBigO.of_bound (‖U x₀‖ * ‖V‖) (Eventually.of_forall fun h => ?_)
      set Δ := F.B (b + 1) (x₀ + h) - F.B (b + 1) x₀ - fderiv ℝ (F.B (b + 1)) x₀ h with hΔ
      calc ‖((U x₀).comp Δ).comp V‖
          ≤ ‖U x₀‖ * ‖Δ‖ * ‖V‖ := by
            refine le_trans (opNorm_comp_le _ _) ?_
            gcongr; exact opNorm_comp_le _ _
        _ = ‖U x₀‖ * ‖V‖ * ‖Δ‖ := by ring
    exact hbig.trans_isLittleO hlo
  have := he₁.sub he₂
  refine this.congr_left fun h => ?_
  exact (hsplit h).symm
end FriedCrossing.Scale
