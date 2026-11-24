-- Prove2me | solution 1 for Formalism.ZF.zfo_M_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:44.595049+00:00
-- url     : https://prove2.me/submissions/d65d920b-c76e-43e5-858e-3f1123b75e74

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Theorems.Thm_Formalism_ZF_zfo_growth_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (hG : ZetaGrowth) (hI : ZetaInvBound) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hσK : 2 / (σ - 1) ≤ 20000 * (T + 2)) (hT : 3 ≤ T) (hτ : 3 ≤ |τ|) (hτT : |τ| ≤ 2 * T) :
    ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ (T + 2) ^ 10 * ‖riemannZeta ((σ : ℂ) + τ * I)‖ := by
  intro w hw
  have hzw := zfo_growth_ball hG hσ1 hσ2 hτ hτT hw
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hinv := hI s hs1
  rw [hsre] at hinv
  have hσ1' : 0 < σ - 1 := by linarith
  have hA : 0 < T + 2 := by linarith
  have ha0 : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs1)
  have h1 : 1 ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) :=
    calc (1 : ℝ) = ‖riemannZeta s‖ * ‖riemannZeta s‖⁻¹ := (mul_inv_cancel₀ ha0.ne').symm
      _ ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) := mul_le_mul_of_nonneg_left hinv ha0.le
  rw [mul_div_assoc', le_div_iff₀ hσ1'] at h1
  have h3 : σ - 1 ≤ 2 * ‖riemannZeta s‖ := by nlinarith
  have h4 : 2 ≤ 20000 * (T + 2) * (σ - 1) := by
    rwa [div_le_iff₀ hσ1'] at hσK
  have h5 : 1 ≤ 20000 * (T + 2) * ‖riemannZeta s‖ := by
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 10000 * (T + 2))
    nlinarith
  have h8 : (5 : ℝ) ^ 8 ≤ (T + 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have h6 : 120000 * (T + 2) ^ 2 ≤ (T + 2) ^ 10 := by
    have e : (T + 2) ^ 10 = (T + 2) ^ 2 * (T + 2) ^ 8 := by ring
    have := mul_le_mul_of_nonneg_left h8 (sq_nonneg (T + 2))
    rw [e]
    norm_num at this ⊢
    nlinarith [sq_nonneg (T + 2)]
  calc ‖riemannZeta w‖ ≤ 6 * (T + 2) := hzw
    _ ≤ 6 * (T + 2) * (20000 * (T + 2) * ‖riemannZeta s‖) := le_mul_of_one_le_right (by linarith) h5
    _ = 120000 * (T + 2) ^ 2 * ‖riemannZeta s‖ := by ring
    _ ≤ (T + 2) ^ 10 * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right h6 ha0.le
end Formalism.ZF
