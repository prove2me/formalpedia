-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zeta_neg_log_deriv_re_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:37.177838+00:00
-- url     : https://prove2.me/submissions/8c06ca8f-4800-4d78-8ac7-066aef8ad356

import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaLogDerivLandauBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_re_le_norm
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_log_deriv_landau_bound
import Theorems.Thm_Formalism_ZF_logDerivRegion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + K * Real.log (|t| + 2) := by
  obtain ⟨c, C, hc, hreg⟩ := Formalism.ZF.logDerivRegion
  obtain ⟨K₃, hK₃⟩ : ∃ k : ℝ, k = ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((6 / 5 : ℝ) : ℂ) n‖ := ⟨_, rfl⟩
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨840 + |C| * Real.log 4 + |K₃|,
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hlog4)) (abs_nonneg _), ?_⟩
  intro σ t hσ hσ2
  have hre1 : 0 ≤ ((σ : ℂ) - 1 + t * I).re := by simp; linarith
  have hR := re_one_div_nonneg hre1
  have hL0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hC0 : 0 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := mul_nonneg (mul_nonneg (abs_nonneg _) hlog4) hL0
  have hK30 : 0 ≤ |K₃| * Real.log (|t| + 2) := mul_nonneg (abs_nonneg _) hL0
  have h840 : 0 ≤ 840 * Real.log (|t| + 2) := mul_nonneg (by norm_num) hL0
  rcases le_or_gt |t| 2 with ht | ht
  ·
    have hs1 : ((σ : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have hsre : ((σ : ℂ) + t * I).re = σ := by simp
    have hLpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
    have hcond : 1 - c / Real.log (|((σ : ℂ) + t * I).im| + 2) ≤ ((σ : ℂ) + t * I).re := by
      rw [him, hsre]; have := div_nonneg hc.le hLpos.le; linarith
    have hb := hreg _ hs1 hcond
    rw [him] at hb
    have es : (σ : ℂ) + t * I - 1 = (σ : ℂ) - 1 + t * I := by ring
    rw [es] at hb
    have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) +
      1 / ((σ : ℂ) - 1 + t * I))
    have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
        (1 / ((σ : ℂ) - 1 + t * I)).re + (-(deriv riemannZeta ((σ : ℂ) + t * I) /
          riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))).re := by
      simp only [Complex.neg_re, Complex.add_re]; ring
    have hL4 : Real.log (|t| + 2) ≤ Real.log 4 :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hCL : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := by
      have h1 : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log (|t| + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      have h2 : |C| * (Real.log (|t| + 2) * Real.log (|t| + 2)) ≤ |C| * (Real.log 4 * Real.log (|t| + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL4 hL0) (abs_nonneg C)
      nlinarith
    rw [hsplit]
    nlinarith
  rcases le_or_gt σ (6 / 5) with hσ' | hσ'
  ·
    have := zeta_log_deriv_landau_bound t σ ht hσ hσ'
    nlinarith
  ·
    have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
    have hLs := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
    rw [neg_div] at hLs
    rw [← hLs]
    have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
    have hsum0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((6 / 5 : ℝ) : ℂ))
      (by rw [Complex.ofReal_re]; norm_num)
    have hbd : (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re ≤ K₃ := by
      calc (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re
          ≤ ‖LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖ :=
            Complex.re_le_norm _
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((6 / 5 : ℝ) : ℂ) n‖ :=
            Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simp; linarith) n)
              (summable_norm_iff.mpr hsum) (summable_norm_iff.mpr hsum0)
        _ = K₃ := hK₃.symm
    have hL1 : 1 ≤ Real.log (|t| + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hK3 : K₃ ≤ |K₃| * Real.log (|t| + 2) := by
      have := mul_le_mul_of_nonneg_left hL1 (abs_nonneg K₃)
      linarith [le_abs_self K₃]
    nlinarith
end Formalism.ZeroFreeDirichlet
