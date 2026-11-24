-- Prove2me | solution 1 for Formalism.ZF.zfo_growth_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:12.539686+00:00
-- url     : https://prove2.me/submissions/48d077aa-7caf-414d-8d21-8c4490edc938

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZfoGrowthBall
import Theorems.Thm_Formalism_ZF_zfo_ball_facts
import Theorems.Thm_Formalism_ZF_zfo_ball_ne_one

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
theorem _root_.solution (hG : ZetaGrowth) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hτ : 3 ≤ |τ|)
    (hτT : |τ| ≤ 2 * T) {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    ‖riemannZeta w‖ ≤ 6 * (T + 2) := by
  obtain ⟨hre, -, hn⟩ := zfo_ball_facts hw
  obtain ⟨hne, him2⟩ := zfo_ball_ne_one hτ hw
  have hre' : 1 / 2 < w.re := by
    have := (abs_le.mp hre).1
    linarith
  have h1 : 5 / 2 ≤ ‖w - 1‖ := by
    have h' : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h'
    linarith
  have hinv1 : 1 / ‖w - 1‖ ≤ 2 / 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / w.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hσabs : |σ| = σ := abs_of_pos (by linarith)
  have hnw : ‖w‖ ≤ 2 * T + 5 / 2 := by
    rw [hσabs] at hn
    linarith
  have hc0 : 0 ≤ 1 + 1 / w.re := by
    have : 0 < 1 / w.re := one_div_pos.mpr (by linarith)
    linarith
  have hprod : ‖w‖ * (1 + 1 / w.re) ≤ (2 * T + 5 / 2) * 3 :=
    mul_le_mul hnw (by linarith) hc0 (by linarith [abs_nonneg τ])
  have hg := hG w (by linarith) hne
  linarith
end Formalism.ZF
