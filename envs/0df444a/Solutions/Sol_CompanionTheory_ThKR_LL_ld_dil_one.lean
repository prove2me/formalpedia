-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.ld_dil_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:49.8458+00:00
-- url     : https://prove2.me/submissions/929fc1db-eb6d-41c2-b3b0-e7b4bfe5aace

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Theorems.Thm_CompanionTheory_ThKR_LL_exists_lip
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_differentiableAt
import Theorems.Thm_CompanionTheory_ThKR_LL_exists_decay
import Theorems.Thm_CompanionTheory_ThKR_LL_hasDerivAt_schwartz_to_L2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {H : ℝ → Eu l →L[ℝ] Eu l} {H' : Eu l →L[ℝ] Eu l} {t₀ : ℝ} (h : HasDerivAt H H' t₀) (h0 : H t₀ = 1)
    (f : Sch l) {F : ℝ → Sch l} (hF : ∀ᶠ t in 𝓝 t₀, ∀ x, F t x = f (H t x)) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l (vf H' f)) t₀ := by
  obtain ⟨K, hK, hb⟩ := exists_lip h
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C, hC, hf⟩ := exists_decay (fderivCLM ℝ (Eu l) ℂ f) (N + 1)
  refine hasDerivAt_schwartz_to_L2 (C := 2 ^ (N + 1) * C * K) (fun x => ?_) ?_
  · have h1 : HasDerivAt (fun t => H t x) (H' x) t₀ := by simpa using h.clm_apply (hasDerivAt_const t₀ x)
    have h2 := (f.hasFDerivAt (H t₀ x)).comp_hasDerivAt t₀ h1
    rw [h0] at h2
    exact h2.congr_of_eventuallyEq (hF.mono fun t ht => ht x)
  · have hs : ∀ᶠ t in 𝓝 t₀, ‖H t - H t₀‖ ≤ 1 / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h.continuousAt).eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
      exact this
    filter_upwards [hb, hF, hs] with t ht hFt hst x
    rw [← hN, hFt, hF.self_of_nhds, h0]
    have e : ‖H t x - x‖ ≤ ‖H t - H t₀‖ * ‖x‖ := by
      have := (H t - H t₀).le_opNorm x
      rw [ContinuousLinearMap.sub_apply] at this
      simpa only [h0, ContinuousLinearMap.one_apply] using this
    have hw : 0 < 1 + ‖x‖ := by positivity
    have hm := (convex_closedBall x (‖x‖ / 2)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f)
      (C := 2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1)) (x := x) (y := H t x) (fun y _ => f.differentiableAt) (fun y hy => by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 1 + ‖x‖ ≤ 2 * (1 + ‖y‖) := by
          have h2 := norm_sub_norm_le x y
          rw [mem_closedBall_iff_norm'] at hy
          linarith
        calc _ ≤ ‖fderiv ℝ f y‖ * (2 * (1 + ‖y‖)) ^ (N + 1) := by gcongr
          _ = 2 ^ (N + 1) * ((1 + ‖y‖) ^ (N + 1) * ‖fderiv ℝ f y‖) := by rw [mul_pow]; ring
          _ ≤ _ := by gcongr; exact hf y)
      (Metric.mem_closedBall_self (by positivity)) (by
        rw [mem_closedBall_iff_norm]
        nlinarith [norm_nonneg x])
    have e2 : ‖H t x - x‖ ≤ K * |t - t₀| * (1 + ‖x‖) := e.trans (by gcongr; simp)
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ (N + 1) * C / (1 + ‖x‖) ^ (N + 1) * (K * |t - t₀| * (1 + ‖x‖))) := by
          refine mul_le_mul_of_nonneg_left (hm.trans ?_) (by positivity)
          gcongr
      _ = _ := by rw [pow_succ (1 + ‖x‖) N]; field_simp
end CompanionTheory.ThKR.LL
