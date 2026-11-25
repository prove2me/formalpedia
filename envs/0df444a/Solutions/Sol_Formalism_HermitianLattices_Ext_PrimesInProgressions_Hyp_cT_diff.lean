-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cT_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:36.378957+00:00
-- url     : https://prove2.me/submissions/47715e1d-ec48-48fd-8a05-80fb2f0996b6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_lw_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_diff2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU0 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hlU : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases (show 2 ≤ U ∨ U = 1 by omega) with h2 | h1
  · have h := cT_diff2 χ hχ U V h2 hUV
    have e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) := by unfold lw; push_cast; rfl
    rw [e] at h
    have : Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) := by positivity
    calc _ ≤ _ := h
      _ ≤ 2 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by nlinarith
  · subst h1
    rcases (show V = 1 ∨ 2 ≤ V by omega) with hv | hv
    · subst hv; simp only [sub_self, norm_zero]; positivity
    · have hA := cT_diff2 χ hχ 2 V le_rfl hv
      have hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2 := by
        rw [cT_sub χ 1 2 (by norm_num)]
        have e : Ioc 1 2 = {2} := by decide
        rw [e, Finset.sum_singleton]
        rw [norm_mul, Complex.norm_real]
        have hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hl : ‖lw 2‖ ≤ 1 / 2 := by
          rw [Real.norm_of_nonneg (lw_nonneg 2)]
          unfold lw; push_cast
          have := Real.log_two_lt_d9
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
        calc _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul hc hl (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      have hl3 : lw 3 ≤ 2 / 3 := by
        unfold lw; push_cast
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      have hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1) := by ring
      rw [hsplit]
      have hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ)) := Real.log_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2 := by
        push_cast; push_cast at hl2
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      calc _ ≤ ‖cT χ V - cT χ 2‖ + ‖cT χ 2 - cT χ 1‖ := norm_add_le _ _
        _ ≤ 2 * ((q : ℝ) + 1) * (2 / 3) + 1 / 2 := by
          have : 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3) :=
            mul_le_mul_of_nonneg_left hl3 (by positivity)
          linarith
        _ ≤ _ := by nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
