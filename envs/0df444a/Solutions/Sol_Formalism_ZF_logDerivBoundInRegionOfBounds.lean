-- Prove2me | solution 1 for Formalism.ZF.logDerivBoundInRegionOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:19.740812+00:00
-- url     : https://prove2.me/submissions/a90f2fb0-f7ee-49ed-b11d-827fc0055180

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrMid
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRegionOf
import Theorems.Thm_Formalism_ZF_ldr_mid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : LogDerivRegionOf := by
  intro hZF hLR hG hI hSH hLL
  obtain ⟨c₀, hc₀, hZ0⟩ := hZF
  obtain ⟨CR, hCR0, hCR⟩ := hLR
  obtain ⟨cS, CS, hcS, hCS⟩ := hSH (Real.exp 24)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set c := min (min (c₀ / 4) 1) (cS * Real.log 2) with hc
  have hcpos : 0 < c := lt_min (lt_min (by linarith) one_pos) (mul_pos hcS (by linarith))
  have hc1 : c ≤ c₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ cS * Real.log 2 := min_le_right _ _
  have hK1 : 0 ≤ 1441 + 60 / c₀ := by positivity
  have hK3 : 0 ≤ 4 * |CS| := by positivity
  refine ⟨c, (1441 + 60 / c₀) + (4 + 4 * CR) + 4 * |CS|, hcpos, ?_⟩
  intro s hs1 hreg
  have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
  set σ := s.re with hσ
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 1 / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLsq : 1 / 4 ≤ L ^ 2 := by nlinarith
  by_cases hright : 1 + 1 / L < σ
  · have hinvpos : 0 < 1 / L := by positivity
    have hσ1 : 1 < σ := by linarith
    have h1 := hCR s hσ1
    have hnorm : σ - 1 ≤ ‖s - 1‖ := by
      have : (s - 1).re = σ - 1 := by simp [hσ]
      calc σ - 1 = (s - 1).re := this.symm
        _ ≤ |(s - 1).re| := le_abs_self _
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hσL : 1 / (σ - 1) ≤ L := by
      rw [div_le_iff₀ (by linarith)]
      have h := hright
      have : 1 / L < σ - 1 := by linarith
      rw [div_lt_iff₀ hL0] at this
      linarith
    have h2 : ‖1 / (s - 1)‖ ≤ L := by
      rw [norm_div, norm_one]
      calc 1 / ‖s - 1‖ ≤ 1 / (σ - 1) := one_div_le_one_div_of_le (by linarith) hnorm
        _ ≤ L := hσL
    calc ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
        ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ (1 / (σ - 1) + CR) + L := add_le_add h1 h2
      _ ≤ (4 + 4 * CR) * L ^ 2 := by nlinarith [mul_nonneg hCR0 (sq_nonneg L)]
      _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hK3 (sq_nonneg L)]
  · push_neg at hright
    by_cases hbig : 24 ≤ L
    · have hlo : 1 - (c₀ / 4) / L ≤ σ := by
        have : c / L ≤ (c₀ / 4) / L := by gcongr
        linarith
      have hlo' : 1 - 1 / L ≤ σ := by
        have : c / L ≤ 1 / L := by gcongr
        linarith
      have hm := Formalism.ZF.ldr_mid hZ0 hc₀ hG hI hLL (σ := σ) (t := t) hbig hlo hlo' hright
      rw [hs]
      calc _ ≤ (1441 + 60 / c₀) * L ^ 2 := hm
        _ ≤ _ := by nlinarith [mul_nonneg hK3 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]
    · push_neg at hbig
      have htT : |t| ≤ Real.exp 24 := by
        have : |t| + 2 < Real.exp 24 := by
          rw [← Real.log_lt_iff_lt_exp (by positivity)]
          exact hbig
        linarith
      have hcL : c / L ≤ cS := by
        rw [div_le_iff₀ hL0]
        nlinarith
      have hinv : 1 / L ≤ 2 := by
        rw [div_le_iff₀ hL0]; linarith
      have hσ3 : σ ≤ 3 := by linarith
      have hb := hCS s hs1 htT (by linarith) hσ3
      calc _ ≤ CS := hb
        _ ≤ |CS| := le_abs_self _
        _ ≤ 4 * |CS| * L ^ 2 := by nlinarith [abs_nonneg CS]
        _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]
end Formalism.ZF
