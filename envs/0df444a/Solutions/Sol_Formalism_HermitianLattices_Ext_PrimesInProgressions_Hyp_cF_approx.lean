-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:23.265796+00:00
-- url     : https://prove2.me/submissions/e86153e0-2f6a-4502-a672-db32a054b79b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_main
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cS_approx


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
theorem _root_.solution (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N))‖ ≤
      26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by
  have hU : 1 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
  have hUN : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have hlt : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUR : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hU
  have hs0 : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNR
  have hsq : √(N : ℝ) < (Nat.sqrt N : ℝ) + 1 := by
    have h := Real.sqrt_lt_sqrt (by positivity)
      (show (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) by exact_mod_cast hlt)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hsq2 : (Nat.sqrt N : ℝ) ≤ √(N : ℝ) := by
    have h := Real.sqrt_le_sqrt (show ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) ≤ N by exact_mod_cast hUN)
    rwa [Real.sqrt_mul_self (by positivity)] at h
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hγ0 : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 1 := by
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hc : 0 ≤ Real.log N + Real.eulerMascheroniConstant := by linarith
  have h1 := cF_main χ hχ N (Nat.sqrt N) hU hUN
  have h2 := cS_approx χ hχ (Nat.sqrt N) hU
  have hdec : cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        DirichletCharacter.LFunction χ 1 - cT χ (Nat.sqrt N)) =
      (cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) - cT χ (Nat.sqrt N))) +
        ((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1) := by
    ring
  rw [hdec]
  have hw : 1 / (Nat.sqrt N : ℝ) ≤ 2 * (1 / √(N : ℝ)) := by
    have h := one_div_le_one_div_of_le hs0 (show √(N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) by linarith)
    calc 1 / (Nat.sqrt N : ℝ) = 2 * (1 / (2 * (Nat.sqrt N : ℝ))) := by field_simp
      _ ≤ 2 * (1 / √(N : ℝ)) := by linarith
  have hv : (Nat.sqrt N : ℝ) / N ≤ 1 / √(N : ℝ) := by
    calc (Nat.sqrt N : ℝ) / N = (Nat.sqrt N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by
          rw [Real.mul_self_sqrt hNR.le]
      _ ≤ √(N : ℝ) / (√(N : ℝ) * √(N : ℝ)) := by gcongr
      _ = 1 / √(N : ℝ) := by field_simp
  calc _ ≤ ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ (Nat.sqrt N) -
          cT χ (Nat.sqrt N))‖ + ‖((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) *
          (cS χ (Nat.sqrt N) - DirichletCharacter.LFunction χ 1)‖ := norm_add_le _ _
    _ ≤ (2 * (Nat.sqrt N : ℝ) / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / (Nat.sqrt N : ℝ)) +
          (Real.log N + Real.eulerMascheroniConstant) * (4 * ((q : ℝ) + 1) / (Nat.sqrt N : ℝ)) := by
        refine add_le_add h1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left h2 hc
    _ = 2 * ((Nat.sqrt N : ℝ) / N) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (1 / (Nat.sqrt N : ℝ)) := by
        ring
    _ ≤ 2 * (1 / √(N : ℝ)) + (8 * ((q : ℝ) + 1) * (1 + Real.log N) +
          4 * ((q : ℝ) + 1) * (Real.log N + Real.eulerMascheroniConstant)) * (2 * (1 / √(N : ℝ))) := by
        gcongr
    _ ≤ 26 * ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) := by
        have hZ : 0 ≤ 1 / √(N : ℝ) := by positivity
        have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        have a3 : ((q : ℝ) + 1) * (1 / √(N : ℝ)) * Real.eulerMascheroniConstant ≤
            ((q : ℝ) + 1) * (1 / √(N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hγ1 (by positivity)
        have a4 : 1 * (1 / √(N : ℝ)) ≤ ((q : ℝ) + 1) * (Real.log N + 1) * (1 / √(N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hZ
        nlinarith
    _ = 26 * ((q : ℝ) + 1) * (Real.log N + 1) / √(N : ℝ) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
