-- Prove2me | solution 1 for Formalism.ZF.zfo_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:28:30.064231+00:00
-- url     : https://prove2.me/submissions/63d7257f-51e9-4092-84ca-6b295bb666f9

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoTermReNonneg
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoNegReLeNorm
import Theorems.Thm_Formalism_ZF_zfo_neg_re_le_norm
import Theorems.Thm_Formalism_ZF_zfo_M_bound
import Theorems.Thm_Formalism_ZF_zfo_diff_ball
import Theorems.Thm_Formalism_ZF_zfo_landau
import Theorems.Thm_Formalism_ZF_zfo_zero_re_lt


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
theorem _root_.solution (h341 : ThreeFourOne) (hLDR : LogDerivRight) (hG : ZetaGrowth)
    (hI : ZetaInvBound) (hLL : LandauLocal) :
    ∃ t₀ : ℝ, 3 ≤ t₀ ∧ ∀ β t : ℝ, t₀ ≤ |t| → riemannZeta ((β : ℂ) + t * I) = 0 →
      β < 1 - (1 / 200000) / Real.log (|t| + 2) := by
  obtain ⟨C, hC0, hC⟩ := hLDR
  refine ⟨max 3 (Real.exp (3 * C)), le_max_left _ _, fun β t ht hzero => ?_⟩
  have hT3 : 3 ≤ |t| := le_trans (le_max_left _ _) ht
  have hTe : Real.exp (3 * C) ≤ |t| := le_trans (le_max_right _ _) ht
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (|t| + 2) := ⟨_, rfl⟩
  rw [← hLdef]
  have hL1 : 1 < L := by
    rw [hLdef, Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hLC : 3 * C ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hLT : L ≤ |t| + 2 := by
    rw [hLdef]
    have := Real.log_le_sub_one_of_pos (show 0 < |t| + 2 by linarith)
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + (1 / 10000) / L := ⟨_, rfl⟩
  have hsm : 0 < (1 / 10000) / L := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hsm1 : (1 / 10000) / L ≤ 1 := by
    rw [div_le_one hL0]
    linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσinv : 1 / (σ - 1) = 10000 * L := by
    rw [hσdef, show (1 : ℝ) + 1 / 10000 / L - 1 = (1 / 10000) / L by ring, one_div_div]
    ring
  have hσK : 2 / (σ - 1) ≤ 20000 * (|t| + 2) := by
    have : 2 / (σ - 1) = 2 * (1 / (σ - 1)) := by ring
    rw [this, hσinv]
    linarith
  have hτ2 : 3 ≤ |2 * t| := by
    rw [abs_mul]
    norm_num
    linarith
  have hτ2T : |2 * t| ≤ 2 * |t| := by
    rw [abs_mul]
    norm_num
  have hM1 : (1 : ℝ) ≤ (|t| + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨S1, hS10, hS1, hS1z⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hT3)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hT3 (by linarith))
  obtain ⟨S2, hS20, hS2, -⟩ := zfo_landau hLL hσ1 hM1 (zfo_diff_ball hτ2)
    (zfo_M_bound hG hI hσ1 hσ2 hσK hT3 hτ2 hτ2T)
  have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = (σ : ℂ) + 2 * t * I := by
    push_cast
    ring
  rw [e2] at hS2
  have hlogM : Real.log ((|t| + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow, hLdef]
    push_cast
    ring
  rw [hlogM] at hS1 hS2
  have h341' := h341 σ t hσ1
  have hR1 : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤ 1 / (σ - 1) + C := by
    have h := hC (σ : ℂ) (by simpa using hσ1)
    simp only [Complex.ofReal_re] at h
    exact (zfo_neg_re_le_norm _).trans h
  rw [hσinv] at hR1
  have hβσ : β < σ := by
    have := zfo_zero_re_lt (ρ := (β : ℂ) + t * I) hσ1 hzero
    simpa using this
  by_cases hcase : σ - β ≤ 1 / 6
  · have hA := hS1z β hzero hcase
    have hd : 0 < σ - β := by linarith
    have key : 4 * (1 / (σ - β)) ≤ 37201 * L := by linarith
    rw [mul_one_div, div_le_iff₀ hd] at key
    have h3 : (21 / 200000) / L < σ - β := by
      rw [div_lt_iff₀ hL0]
      nlinarith
    have h4 : (21 / 200000) / L = (1 / 200000) / L + (1 / 10000) / L := by ring
    linarith
  · push_neg at hcase
    have h4 : (1 / 10000) / L ≤ 1 / 10000 := div_le_self (by norm_num) hL1.le
    have h5 : (1 / 200000) / L ≤ 1 / 200000 := div_le_self (by norm_num) hL1.le
    linarith
end Formalism.ZF
